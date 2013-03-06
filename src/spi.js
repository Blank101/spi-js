/*!
 * Copyright (c) 2012 Sam MacPherson
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * 
 * SandBoxd Public Interface Client API Library
 * JavaScript Implementation
 */

/** @namespace */
var SPI = function () {
	/** @private */
	var config = {
			host:null,
			gameid:null,
			apiKey:null
	};
	
	/** @private */
	var applyRequest = function (request, resultFormatter, asynch, timeout) {
		if (asynch != null) {
			//Asynchronous call
			request.send(function (response) {
				var data;
				try { data = response.parseXML(); } catch (e) { return; }
				if (!response.isFault()) {
					if (asynch.response != null) asynch.response(resultFormatter(data));
				} else {
					if (asynch.error != null) asynch.error({errorCode:data.faultCode, errorString:data.faultString});
				}
			}, timeout);
			
			return null;
		} else {
			//Synchronous call
			var response = request.send(null, timeout);
			var data;
			try { data = response.parseXML(); } catch (e) { return; }
			
			if (!response.isFault()) {
				return resultFormatter(data);
			} else {
				throw {errorCode:data.faultCode, errorString:data.faultString};
			}
		}
	};
	
	/** @private */
	var SHA1 = function SHA1 (msg) {
	 
		function rotate_left(n,s) {
			var t4 = ( n<<s ) | (n>>>(32-s));
			return t4;
		};
	 
		function lsb_hex(val) {
			var str="";
			var i;
			var vh;
			var vl;
	 
			for( i=0; i<=6; i+=2 ) {
				vh = (val>>>(i*4+4))&0x0f;
				vl = (val>>>(i*4))&0x0f;
				str += vh.toString(16) + vl.toString(16);
			}
			return str;
		};
	 
		function cvt_hex(val) {
			var str="";
			var i;
			var v;
	 
			for( i=7; i>=0; i-- ) {
				v = (val>>>(i*4))&0x0f;
				str += v.toString(16);
			}
			return str;
		};
	 
	 
		function Utf8Encode(string) {
			string = string.replace(/\r\n/g,"\n");
			var utftext = "";
	 
			for (var n = 0; n < string.length; n++) {
	 
				var c = string.charCodeAt(n);
	 
				if (c < 128) {
					utftext += String.fromCharCode(c);
				}
				else if((c > 127) && (c < 2048)) {
					utftext += String.fromCharCode((c >> 6) | 192);
					utftext += String.fromCharCode((c & 63) | 128);
				}
				else {
					utftext += String.fromCharCode((c >> 12) | 224);
					utftext += String.fromCharCode(((c >> 6) & 63) | 128);
					utftext += String.fromCharCode((c & 63) | 128);
				}
	 
			}
	 
			return utftext;
		};
	 
		var blockstart;
		var i, j;
		var W = new Array(80);
		var H0 = 0x67452301;
		var H1 = 0xEFCDAB89;
		var H2 = 0x98BADCFE;
		var H3 = 0x10325476;
		var H4 = 0xC3D2E1F0;
		var A, B, C, D, E;
		var temp;
	 
		msg = Utf8Encode(msg);
	 
		var msg_len = msg.length;
	 
		var word_array = new Array();
		for( i=0; i<msg_len-3; i+=4 ) {
			j = msg.charCodeAt(i)<<24 | msg.charCodeAt(i+1)<<16 |
			msg.charCodeAt(i+2)<<8 | msg.charCodeAt(i+3);
			word_array.push( j );
		}
	 
		switch( msg_len % 4 ) {
			case 0:
				i = 0x080000000;
			break;
			case 1:
				i = msg.charCodeAt(msg_len-1)<<24 | 0x0800000;
			break;
	 
			case 2:
				i = msg.charCodeAt(msg_len-2)<<24 | msg.charCodeAt(msg_len-1)<<16 | 0x08000;
			break;
	 
			case 3:
				i = msg.charCodeAt(msg_len-3)<<24 | msg.charCodeAt(msg_len-2)<<16 | msg.charCodeAt(msg_len-1)<<8	| 0x80;
			break;
		}
	 
		word_array.push( i );
	 
		while( (word_array.length % 16) != 14 ) word_array.push( 0 );
	 
		word_array.push( msg_len>>>29 );
		word_array.push( (msg_len<<3)&0x0ffffffff );
	 
	 
		for ( blockstart=0; blockstart<word_array.length; blockstart+=16 ) {
	 
			for( i=0; i<16; i++ ) W[i] = word_array[blockstart+i];
			for( i=16; i<=79; i++ ) W[i] = rotate_left(W[i-3] ^ W[i-8] ^ W[i-14] ^ W[i-16], 1);
	 
			A = H0;
			B = H1;
			C = H2;
			D = H3;
			E = H4;
	 
			for( i= 0; i<=19; i++ ) {
				temp = (rotate_left(A,5) + ((B&C) | (~B&D)) + E + W[i] + 0x5A827999) & 0x0ffffffff;
				E = D;
				D = C;
				C = rotate_left(B,30);
				B = A;
				A = temp;
			}
	 
			for( i=20; i<=39; i++ ) {
				temp = (rotate_left(A,5) + (B ^ C ^ D) + E + W[i] + 0x6ED9EBA1) & 0x0ffffffff;
				E = D;
				D = C;
				C = rotate_left(B,30);
				B = A;
				A = temp;
			}
	 
			for( i=40; i<=59; i++ ) {
				temp = (rotate_left(A,5) + ((B&C) | (B&D) | (C&D)) + E + W[i] + 0x8F1BBCDC) & 0x0ffffffff;
				E = D;
				D = C;
				C = rotate_left(B,30);
				B = A;
				A = temp;
			}
	 
			for( i=60; i<=79; i++ ) {
				temp = (rotate_left(A,5) + (B ^ C ^ D) + E + W[i] + 0xCA62C1D6) & 0x0ffffffff;
				E = D;
				D = C;
				C = rotate_left(B,30);
				B = A;
				A = temp;
			}
	 
			H0 = (H0 + A) & 0x0ffffffff;
			H1 = (H1 + B) & 0x0ffffffff;
			H2 = (H2 + C) & 0x0ffffffff;
			H3 = (H3 + D) & 0x0ffffffff;
			H4 = (H4 + E) & 0x0ffffffff;
	 
		}
	 
		var temp = cvt_hex(H0) + cvt_hex(H1) + cvt_hex(H2) + cvt_hex(H3) + cvt_hex(H4);
	 
		return temp.toLowerCase();
	};
	
	/** @private */
	var VALID_NONCE_CHARS = ['a', 'b', 'c' , 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];
	var generateNonce = function () {
		var str = "";
		for (var i = 0; i < 10; i++) {
			str += VALID_NONCE_CHARS[Math.floor(Math.random() * VALID_NONCE_CHARS.length)];
		}
		return str;
	};
	
	/** @private */
	var addHeader = function (request) {
		var nonce = generateNonce();
		
		request.addParam(SPI.VERSION);
		request.addParam(config.gameid);
		request.addParam(SHA1(config.apiKey + nonce));
		request.addParam(nonce);
	};
	
	/** @scope SPI */
	return 	{
		//Api version number
		
		VERSION: "1.0",
		
		//SPI Errors
		
		ERR_USER_DOES_NOT_EXIST: 1,
		ERR_SESSION_NOT_VALID: 2,
		ERR_GROUP_DOES_NOT_EXIST: 3,
		ERR_ACHIEVEMENT_DOES_NOT_EXIST: 4,
		ERR_USER_NOT_REGISTERED: 5,
		ERR_STAT_DOES_NOT_EXIST: 6,
		ERR_GAME_DOES_NOT_EXIST: 7,
		ERR_API_KEY_NOT_VALID: 8,
		ERR_IP_NOT_VALID: 9,
		ERR_INVALID_FUNCTION: 10,
		ERR_UNKNOWN: 11,
		ERR_VERSION: 12,
		ERR_TRANSACTION_EXISTS: 13,
		ERR_TRANSACTION_DECLINED: 14,
		ERR_GUESTS_INVALID: 15,
		ERR_INPUT: 16,
		
		/**
		 * <p>
		 * Initialize SPI.
		 * </p>
		 * 
		 * @param {String} host The address of the SandBoxd Public Interface.
		 * @param {Number} [gameid] The gameid for this game. If not specified then we are in dev mode.
		 * @param {String} [apiKey] The api key for this game. No need to specify if we are in dev mode.
		 */
		init: function (host, gameid, apiKey) {
			if (gameid == undefined) {
				gameid = 0;
				apiKey = "";
			}
			
			config.host = host;
			config.gameid = Number(gameid);
			config.apiKey = apiKey;
		},
		
		/**
		 * <p>
		 * Retrieve a user object.
		 * </p>
		 * 
		 * @param {Number} uid The user id for the user object you want to retrieve.
		 * @param {String} [sid] The session id of this user. This is used to verify the user and get the microids that the user has purchased.
		 * @param {String} [ip] The user's public ip address. Used as an additional security measure.
		 * @param [asynch] An optional object which contains both a response and error value which act as callbacks for asynchronous communication. If not specified then the call is synchronous.
		 * 
		 * @returns A user object.
		 */
		getUser: function (uid, sid, ip, asynch) {
			if (uid == undefined) uid = 0;
			
			var request = new XmlRpcRequest(config.host, "spi.getuser");
			addHeader(request);
			request.addParam(Number(uid));
			if (sid != null) request.addParam(sid);
			if (ip != null) request.addParam(ip);
			
			return applyRequest(request, function (data) {
				return {uid:uid, sid:sid, name:data[0], avatar:data[1], gid:data[2], friendids:data[3], achievements:data[4], stats:data[5], microids:data[6]};
			}, asynch);
		},
		
		/**
		 * <p>
		 * Retrieve a group object.
		 * </p>
		 * 
		 * @param {Number} gid The group id for the group object you want to retrieve.
		 * @param [asynch] An optional object which contains both a response and error value which act as callbacks for asynchronous communication. If not specified then the call is synchronous.
		 * 
		 * @return A group object.
		 */
		getGroup: function (gid, asynch) {
			var request = new XmlRpcRequest(config.host, "spi.getgroup");
			addHeader(request);
			request.addParam(Number(gid));
			
			return applyRequest(request, function (data) {
				return {gid:gid, name:data[0], members:data[1]};
			}, asynch);
		},
		
		/**
		 * <p>
		 * Set a user achievement.
		 * </p>
		 * 
		 * @param {Number} uid The user's uid you want to set the achievement for.
		 * @param {String} sid The user's sid.
		 * @param {String} key The key for this achievement.
		 * @param {Number} value The value to set this achievement to.
		 * @param [asynch] An optional object which contains both a response and error value which act as callbacks for asynchronous communication. If not specified then the call is synchronous.
		 */
		setAchievement: function (uid, sid, key, value, asynch) {
			var request = new XmlRpcRequest(config.host, "spi.achievement");
			addHeader(request);
			request.addParam(Number(uid));
			request.addParam(sid);
			request.addParam(key);
			request.addParam(Number(value));
			
			return applyRequest(request, function (data) {
				return null;
			}, asynch);
		},
		
		/**
		 * <p>
		 * Set a user statistic.
		 * </p>
		 * 
		 * @param {Number} uid The user's uid you want to set the statistic for.
		 * @param {String} sid The user's sid.
		 * @param {String} key The key for this statistic.
		 * @param {String} value The value to set this statistic to.
		 * @param [asynch] An optional object which contains both a response and error value which act as callbacks for asynchronous communication. If not specified then the call is synchronous.
		 */
		setStat: function (uid, sid, key, value, asynch) {
			var request = new XmlRpcRequest(config.host, "spi.stat");
			addHeader(request);
			request.addParam(Number(uid));
			request.addParam(sid);
			request.addParam(key);
			request.addParam(value);
			
			return applyRequest(request, function (data) {
				return null;
			}, asynch);
		},
		
		/**
		 * <p>
		 * Set a user's location inside the game.
		 * </p>
		 * 
		 * @param {Number} uid The user's uid you want to set the location for.
		 * @param {String} sid The user's sid.
		 * @param {String} [locationData] The machine name location of the user. If not specified then the user is unreachable within the game.
		 * @param {String} [locationName] The user friendly name of this location.
		 * @param [asynch] An optional object which contains both a response and error value which act as callbacks for asynchronous communication. If not specified then the call is synchronous.
		 */
		setLocation: function (uid, sid, locationData, locationName, asynch) {
			var request = new XmlRpcRequest(config.host, "spi.location");
			addHeader(request);
			request.addParam(Number(uid));
			request.addParam(sid);
			request.addParam(locationData);
			request.addParam(locationName);
			
			return applyRequest(request, function (data) {
				return null;
			}, asynch);
		},
		
		/**
		 * <p>
		 * Apply a microtransaction to a user.
		 * </p>
		 * 
		 * @param {Number} uid The user's uid you want to present with a microtransaction.
		 * @param {String} sid The user's sid.
		 * @param {String} microid A unique identifier for the microtransaction.
		 * @param {String} desc A description of the microtransaction to present to the user.
		 * @param {Number} amount The amount of credits to make this purchase.
		 * @param [asynch] An optional object which contains both a response and error value which act as callbacks for asynchronous communication. If not specified then the call is synchronous.
		 */
		applyTransaction: function (uid, sid, microid, desc, amount, asynch) {
			var request = new XmlRpcRequest(config.host, "spi.transaction");
			addHeader(request);
			request.addParam(Number(uid));
			request.addParam(sid);
			request.addParam(microid);
			request.addParam(desc);
			request.addParam(Number(amount));
			
			return applyRequest(request, function (data) {
				return null;
			}, asynch, 600000);		//10 minutes timeout (This requires user interaction so it could take a while)
		},
		
		/**
		 * <p>
		 * A helper method for retrieving the url query parameters.
		 * </p>
		 * 
		 * @return An object whose keys/values match the keys/values of the query parameters.
		 */
		getQueryParameters: function () {
			var params = {};
			var urlParams = location.search.substr(1).split("&");
			for (var i in urlParams) {
				if (urlParams[i] != "") {
					var keyValue = urlParams[i].split("=");
					params[decodeURI(keyValue[0])] = decodeURI(keyValue[1]);
				}
			}
			return params;
		}
	};
}();