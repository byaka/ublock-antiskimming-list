# -*- coding: utf-8 -*-
import string, sys, traceback, zipfile, os, datetime, time, json, hmac, hashlib, math, random, re, copy, urllib2, urllib, types, decimal, inspect, subprocess
import os.path
from urlparse import *
from urllib import urlencode
from decimal import *
#import typehack
#with typehack we can add methods to build-in classes, as in JS!
#see code.google.com/p/typehack/source/browse/doc/readme.txt
import difflib
from struct import Struct
from operator import xor
from itertools import izip, izip_longest, starmap, imap
#===================================
class magicDict(dict):
   #Реализация объектов-словарей, как в Javascript
   #! http://tomerfiliba.com/recipes/AttrDict/
   def __getattr__(self, attr):
      if attr[:2] is '__': raise AttributeError #for support PICKLE protocol
      return self.get(attr, None)
   # __getattr__=dict.__getitem__
   __setattr__=dict.__setitem__
   __delattr__=dict.__delitem__
   __reduce__=dict.__reduce__

def dict2magic(o, recursive=False):
   if recursive:
      if isArray(o):
         for i, _ in enumerate(o): o[i]=dictToMagic(o[i], recursive=True)
      elif isDict(o):
         for i in o: o[i]=dictToMagic(o[i], recursive=True)
         o=magicDict(o)
   elif isDict(o): o=magicDict(o)
   return o
dictToMagic=dict2magic
###dict.toMagic=dictToMagic
#===================================

true=True
false=False
none=None

noneStr=[None, '',"u'none'",'"none"','u"none"',"'none'","u'None'",'"None"','u"None"',"'None'",'none','None']
translitTable={u'а':'a', u'б':'b', u'в':'v', u'г':'g', u'д':'d', u'е':'e', u'ё':'e', u'ж':'zh', u'з':'z', u'и':'i', u'й':'y', u'к':'k', u'л':'l', u'м':'m', u'н':'n', u'о':'o', u'п':'p', u'р':'r', u'с':'s', u'т':'t', u'у':'u', u'ф':'f', u'х':'kh', u'ц':'ts', u'ч':'ch', u'ш':'sh', u'щ':'shch', u'ы':'y', u'ь':"'", u'ъ':"'", u'э':'e', u'ю':'yu', u'я':'ya'}
uLetters=['A','a','b','B', 'C','c', 'D','d', 'E','e','F','f','G','g','H','h','I','i','J','j','K','k','L','l','M','m','N','n','O','o','P','p','Q','q','U','u','R','r','S','s','T','t','V','v','W','w','X','x','Y','y','Z','z']
uLettersRu=[u'А', u'а', u'Б', u'б', u'В', u'в', u'Г', u'г', u'Д', u'д', u'Е', u'е', u'Ё', u'ё', u'Ж', u'ж', u'З', u'з', u'И', u'и', u'Й', u'й', u'К', u'к', u'Л', u'л', u'М', u'м', u'Н', u'н', u'О', u'о', u'П', u'п', u'Р', u'р', u'С', u'с', u'Т', u'т', u'У', u'у', u'Ф', u'ф', u'Х', u'х', u'Ц', u'ц', u'Ч', u'ч', u'Ш', u'ш', u'Щ', u'щ', u'Ъ', u'ъ', u'Ы', u'ы', u'Ь', u'ь', u'Э', u'э', u'Ю', u'ю', u'Я', u'я']
uPunctuations=[',','.',';',':','!','?']
uSpecials=['"',"'",'<','>','@','#','$','%','^','&','*','(',')','-','_','+','=','[',']','{','}','~','`','|']
uDash=['‐', '−', '‒', '–', '—', '―', '-']
uSpaces=[' ']
uDigits=['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

ucodes={'\\u0430': 'а','\\u0410': 'А','\\u0431': 'б','\\u0411': 'Б','\\u0432': 'в','\\u0412': 'В','\\u0433': 'г','\\u0413': 'Г','\\u0434': 'д','\\u0414': 'Д','\\u0435': 'е','\\u0415': 'Е','\\u0451': 'ё','\\u0401': 'Ё','\\u0436': 'ж','\\u0416': 'Ж','\\u0437': 'з','\\u0417': 'З','\\u0438': 'и','\\u0418': 'И','\\u0439': 'й','\\u0419': 'Й','\\u043a': 'к','\\u041a': 'К','\\u043b': 'л','\\u041b': 'Л','\\u043c': 'м','\\u041c': 'М','\\u043d': 'н','\\u041d': 'Н','\\u043e': 'о','\\u041e': 'О','\\u043f': 'п','\\u041f': 'П','\\u0440': 'р','\\u0420': 'Р','\\u0441': 'с','\\u0421': 'С','\\u0442': 'т','\\u0422': 'Т','\\u0443': 'у','\\u0423': 'У','\\u0444': 'ф','\\u0424': 'Ф','\\u0445': 'х','\\u0425': 'Х','\\u0446': 'ц','\\u0426': 'Ц','\\u0447': 'ч','\\u0427': 'Ч','\\u0448': 'ш','\\u0428': 'Ш','\\u0449': 'щ','\\u0429': 'Щ','\\u044a': 'ъ','\\u042a': 'Ъ','\\u044b': 'ы','\\u042b': 'Ы','\\u044c': 'ь','\\u042c': 'Ь','\\u044d': 'э','\\u042d': 'Э','\\u044e': 'ю','\\u042e': 'Ю','\\u044f': 'я','\\u042f': 'Я'}
usymbols=uLetters+uPunctuations+uSpecials
####
uCodes=ucodes
uSymbols=usymbols

allColors=['alicemblue','antiquewhite','aqua','aquamarine','azure','beige','bisque','black','blanchedalmond','blue','blueviolet','brown','burlywood','cadetblue','chartreuse','chocolate','coral','cornflowerblue','cornsilk','crimson','cyan','darkblue','darkcyan','darkgoldenrod','darkgray','darkgreen','darkkhaki','darkmagenta','darkolivegreen','darkorange','darkochid','darkred','darksalmon','darkseagreen','darkslateblue','darkslategray','darkturquoise','darkviolet','deeppink','deepskyblue','dimgray','dodgerblue','firebrick','floralwhite','forestgreen','fushsia','gainsboro','ghostwhite','gold','goldenrod','gray','green','greenyellow','honeydew','hotpink','indiandred','indigo','ivory','khaki','lavender','lavenderblush','lawngreen','lemonchiffon','ligtblue','lightcoral','lightcyan','lightgoldenrodyellow','lightgreen','lightgrey','lightpink','lightsalmon','lightseagreen','lightscyblue','lightslategray','lightsteelblue','lightyellow','lime','limegreen','linen','magenta','mahogany','maroon','mediumaquamarine','mediumblue','mediumorchid','mediumpurple','mediumseagreen','mediumslateblue','mediumspringgreen','mediumturquoise','medium','midnightblue','mintcream','mistyrose','moccasin','navajowhite','navy','oldlace','olive','olivedrab','orange','orengered','orchid','palegoldenrod','palegreen','paleturquose','palevioletred','papayawhop','peachpuff','peru','pink','plum','powderblue','purple','red','rosybrown','royalblue','saddlebrown','salmon','sandybrown','seagreen','seashell','sienna','silver','skyblue','slateblue','slategray','snow','springgreen','steelblue','tan','teal','thistle','tomato','turquose','violet','wheat','white','whitesmoke','yellow','yellowgreen']
# uCodes={}
for s in uSymbols:
   c=str(hex(ord(s)))[2:]
   while len(c)<4: c='0'+c
   c='\\u'+c
   uCodes[c]=s

regExp_parseFloat=re.compile("-{0,1}[0-9]+([.]{0,1}[0-9]*)", re.U)
regExp_specialSymbols0=re.compile("[\W_]", re.U)
regExp_lettersReplace0=re.compile(u"[А-Яа-я]", re.U)
regExp_hex=re.compile("^[a-f0-9]*$", re.U)
regExp_htmlEncoding=re.compile('<meta .*?charset="?([\w-]*).*?>', re.U)
regExp_isEmail=re.compile('^([a-zA-Z0-9_\.\-\+])+\@(([a-zA-Z0-9\-])+\.)+([a-zA-Z0-9]{2,4})+$', re.U)
# regExp_isURL=re.compile('((([A-Za-z]{3,9}:(?:\/\/)?)(?:[-;:&=\+\$,\w]+@)?[A-Za-z0-9.-]+|(?:www.|[-;:&=\+\$,\w]+@)[A-Za-z0-9.-]+)((?:\/[\+~%\/.\w-_]*)?\??(?:[-\+=&;%@.\w_]*)#?(?:[\w]*))?)', re.U)
regExp_isPassword=re.compile('^[\w_]{6,18}$', re.U)
regExp_anySymbol=re.compile('.{1}', re.U)
regExp_anyText=re.compile('.*', re.U)
regExp_anyWord=re.compile('[a-zA-Zа-яёА-ЯЁ0-9_\-]+', re.U)
regExp_splitEmail=re.compile("[,\s]", re.U)

#===================================
def selfInfo():
   (module,line,name,code)=traceback.extract_stack()[-2]
   return magicDict({'module':module, 'line':line, 'name':name, 'path':getScriptPath()})

def getScriptPath():
   return os.path.dirname(os.path.realpath(sys.argv[0]))

def getScriptName(withExt=False):
   if withExt: return os.path.basename(sys.argv[0])
   else: return os.path.splitext(os.path.basename(sys.argv[0]))[0]
#===================================
def getHtml(url, tryEncode=True, followRedirect=True):
   class NoRedirection(urllib2.HTTPErrorProcessor):
      def http_response(self, request, response):
         code, msg, hdrs = response.code, response.msg, response.info()
         return response
      https_response = http_response
   if followRedirect:
      opener=urllib2.build_opener()
   else:
      opener=urllib2.build_opener(NoRedirection)
   try:
      page=opener.open(url)
      pageHtml=page.read()
   except:
      opener.close()
      return None
   if tryEncode:
      try:
         charset = re.findall('charset=(.*?)$', page.info()['Content-Type'])[0].lower()
         if charset != 'utf-8': pageHtml = pageHtml.decode(charset) #решаем проблему с кодировками
      except: pass
      pageHtml = strUniEncode(pageHtml)
   opener.close()
   return pageHtml

def getSize(obj):
   return sys.getsizeof(obj)

def getHtml2(url, followRedirect=True, headers={}, proxie=None, type='get', timeout=15, returnOnlyData=True, checkHtml=False, logHeadersBefore=False, auth=False, base64Auth=False, data={}, tryForceEncoding=False, forceEncoding=False, cookies=False):
   # print url, data
   import requests
   # from requests.auth import HTTPBasicAuth
   # from requests.auth import HTTPDigestAuth
   try: #работаем с кириллическими доменами
      if re.findall('[а-яА-Я]',url) != []:
         urlArr=urlparse(url.decode('utf-8'))
         import idna
         urlDomain=idna.encode(urlArr.netloc)#.decode('utf-8')
         url=url.replace(urlArr.netloc.encode('utf-8'),urlDomain)
   except:pass
   if proxie and len(proxie):
      if isArray(proxie):
         proxie={'http':'http://%s:%s@%s'%(arrGet(proxie,1) or '', arrGet(proxie,2) or '', proxie[0])}
      else: proxie={'http':'http://%s'%(proxie)}
   if base64Auth:
      import base64
      base64string = base64.encodestring('%s:%s' % (base64Auth[0], base64Auth[1]))[:-1]
      headers={"Authorization":"Basic %s" % base64string}
   if checkHtml: #! Опять женя какуюто херню наворотил, поправить на рекурсивный вызов
      r=requests.head(url, allow_redirects=followRedirect, headers=headers, timeout=timeout, proxies=proxie)
      # if r.status_code != 200:
      #    return magicDict({'status':r.status_code})
      try: contentType=r.headers['content-type'].split(';')[0]
      except: contentType='text/html'
      if contentType!='text/html':
         return magicDict({'status':r.status_code, 'contentType':contentType})
   if isArray(auth): auth=(auth[0], auth[1])
   elif auth: auth=('BuberStats','76d3ca8d538bc44bd5a5aa0c316ff428')
   else: auth=None
   # auth=HTTPDigestAuth(auth[0], auth[1])
   # print auth

   try:
      if(type=='get'):
         r=requests.get(url, allow_redirects=followRedirect, headers=headers, timeout=timeout, proxies=proxie, stream=logHeadersBefore, auth=auth, cookies=cookies)
      elif(type=='post'):
         r=requests.post(url, data=data, allow_redirects=followRedirect, headers=headers, timeout=timeout, proxies=proxie, stream=logHeadersBefore, auth=auth, cookies=cookies)
      if logHeadersBefore: print_r(dict(r.headers))
   except Exception, e:
      print '!!!ошибка запроса'
      return None if returnOnlyData else magicDict({'data':None, 'status':e})
   try: contentType=r.headers['content-type'].split(';')[0]
   except: contentType=None
   text=r.text
   if forceEncoding or (tryForceEncoding and (r.encoding=='ISO-8859-1' or not r.encoding)):
      #ISO-8859-1 проставляется, если сервер не отдал кодировку
      try:
         enc=regExp_htmlEncoding.search(text).group(1) #ищем кодировку в теле ответа
         r.encoding=enc #проставляем эту кодировку для запроса
         text=r.text #получаем ответ заново в правильной кодировке (скарее всего данные не запрашиваются занов, а просто происходит переходирование)
      except: pass
   if returnOnlyData: return text
   else:
      return magicDict({'data':text, 'encoding':r.encoding.lower() if r.encoding else False, 'status':r.status_code, 'contentType':contentType, 'response':r, 'url':r.url, 'cookies':dict(r.cookies), 'headers':dict(r.headers)})
#===================================
def pbkdf2(data,salt,iterations=1000,keylen=6,hashfunc=None):
   return pbkdf2_bin(data,salt,iterations,keylen,hashfunc).encode('hex')

def pbkdf2_bin(data,salt,iterations=1000,keylen=32,hashfunc=None):
   hashfunc=hashfunc or hashlib.sha1
   mac=hmac.new(data,None,hashfunc)
   _pack_int=Struct('>I').pack
   def _pseudorandom(x,mac=mac):
      h=mac.copy()
      h.update(x)
      return map(ord,h.digest())
   buf=[]
   for block in xrange(1,-(-keylen // mac.digest_size)+1):
      rv=u=_pseudorandom(salt+_pack_int(block))
      for i in xrange(iterations-1):
         u=_pseudorandom(''.join(map(chr,u)))
         rv=starmap(xor,izip(rv,u))
      buf.extend(rv)
   return ''.join(map(chr,buf))[:keylen]
#===================================
def randomEx(mult=262144, vals=None, pref='', suf='', soLong=3, cbSoLong=lambda s: s*2):
   if vals is None: vals=[]
   s=pref+str(int(random.random()*mult))+suf
   mytime=getms(False)
   while(s in vals):
      s=pref+str(int(random.random()*mult))+suf
      if getms(False)-mytime>soLong: #защита от бесконечного цикла
         mytime=getms(False)
         print '>>> randomEx generate value so long!'
         if isFunction(cbSoLong):
            mult=cbSoLong(mult)
            if mult is None: return None
         else: return None
   return s

def everyWithEvery(arr, func, onlyIndex=False):
   for i1 in xrange(len(arr)):
      for i2 in xrange(len(arr)):
         if i1==i2: continue
         s=func(i1 if onlyIndex else arr[i1], i2 if onlyIndex else arr[i2])
         if s is False: return False
   return True
EveryWithEvery=everyWithEvery #для обратной совместимости

def intINstr(data, specialAs=None):
   try: data=data.decode('utf-8')
   except: pass
   data=data.replace(' ','')
   if specialAs==None: data=regExp_specialSymbols0.sub('',data)
   elif isString(specialAs): data=regExp_specialSymbols0.sub('a',data)
   else: data=regExp_specialSymbols0.sub('0',data)
   if not len(data): return None
   data=regExp_lettersReplace0.sub('a', data)
   d=[str(t) for t in range(10)]
   try:
      float(data)
      return 'int'
   except: pass
   s=sorted(data, key=lambda i: i in d)
   i=len(s)/2
   if not(len(s)%2) and i<len(s)-1: i=i+1
   if s[i] in d: r='iws'
   elif s[-1] in d: r='swi'
   else: r='str'
   return r

def reRound(val, to=None, asfloat=True):
   to=to or 100
   if(abs(val)<to): return val
   s=val/to
   s=(s-math.floor(s))*to
   if(not(asfloat)): s=round(s)
   return s

def parseFloatEx(s):
   v=regExp_parseFloat.search(s)
   if not v: return 0
   return float(v.group(0))
#===================================
def pointCheck(A,B,C):
   #check, if point C is on left side (>0) or right side(<0) from AB or belong AB (=0)
   return (B[0]-A[0])*(C[1]-B[1])-(B[1]-A[1])*(C[0]-B[0])

def intersectCheck(A,B,C,D):
   s1=pointCheck(A,B,C)*pointCheck(A,B,D)
   s2=pointCheck(C,D,A)*pointCheck(C,D,B)
   return [s1<=0 and s2<=0,s1,s2]

def reAngle(val):
   val=reRound(val,360)
   if(val<=0): val+=360
   return val
#===================================
def stopwatchMark(name='default', clear=False, wait=False, inMS=True):
   if name not in stopwatch['values'] or clear: stopwatch['values'][name]=[]
   stopwatch['values'][name].append(getms(inMS))
   if wait: stopwatch['values'][name].append(None)

def stopwatchShow(name='default', save=True, wait=False, andPrint='%s = %s', inMS=True):
   s=getms(inMS)
   vals=stopwatch['values'][name]
   v=0.0
   for i in xrange(1,len(vals)):
      if vals[i] is None or vals[i-1] is None: continue
      v+=vals[i]-vals[i-1]
   v+=s-vals[-1] if vals[-1] is not None else 0
   # print v
   if save: stopwatchMark(name=name, wait=wait, inMS=inMS)
   if andPrint and isString(andPrint): print andPrint%(name, v)
   return v

def stopwatchShowAll(includeDefault=False, andPrint='%s = %s', printSorted=True):
   v={}
   for k in stopwatch['values'].iterkeys():
      if not includeDefault and k=='default': continue
      v[k]=stopwatchShow(name=k, save=False, andPrint=False)
   stopwatch['values']={'default':[]}
   if isString(andPrint):
      for k in sorted(v.keys(), key=lambda k: v[k], reverse=True):
         print andPrint%(k, v[k])
   return v

global stopwatch
stopwatch=magicDict({'mark':stopwatchMark, 'values':{'default':[]}, 'show':stopwatchShow, 'showAll':stopwatchShowAll})
#===================================
def iterate(cb, o):
   res=[]
   _args, _, _, _=inspect.getargspec(cb)
   _args=[s for s in _args if s!='self']
   for i, s in enumerate(o):
      if len(_args)==1: r=cb(s)
      elif len(_args)==2: r=cb(s, i)
      elif len(_args)==3: r=cb(s, o, i)
      res.append(r)
   return res
#===================================
def inOf(o,i):
   if isArray(o):
      try:
         return o.index(i)+1
      except: return False
   else:
      try:
         if o[i] is not None: return True
         else: return False
      except: return False

def length(obj):
   return len(obj)
###str.length=length
###list.length=length

def isFunction(var):
   return hasattr(var, '__call__')

def isClass(var):
   return isinstance(var, (type, types.ClassType, types.TypeType))

def isModule(var):
   return isinstance(var, (types.ModuleType))

def isModuleBuiltin(var):
   return isModule(var) and getattr(var, '__name__', '') in sys.builtin_module_names

def isString(var):
   return isinstance(var, (str, unicode))

def isBool(var):
   return isinstance(var, (bool))

def isNum(var):
   return isinstance(var, (int, float, long, complex, Decimal))

def isFloat(var):
   return isinstance(var, (float, Decimal))

def isArray(var):
   return isinstance(var, (list))

def isTuple(var):
   return isinstance(var, (tuple))

def isDict(var):
   return isinstance(var, (dict))
isObject=isDict

def isSet(var):
   return isinstance(var, (set))

def json2generator(data, arrayKey=None):
   """
   Функция конвертирует переданный json в генератор. Это позволяет избежать утечки памяти на огромных обьемах данных. Может выдать генератор только для массива (неважно какой вложенности и сложности). arrayKey должен указывать на массив, может быть цепочкой (key1.key2)
   """
   from ijson import common
   # from io import BytesIO
   from cStringIO import StringIO
   #! yajl2 беккенд работает значительно быстрее, но на первый сервак так и не удалось его установить, пишет "Yajl shared object cannot be found"
   try: import ijson.backends.yajl2_cffi as ijson
   except:
      try: from ijson.backends import yajl2 as ijson
      except:
         try: from ijson.backends import yajl as ijson
         except: from ijson.backends import python as ijson
   try: f=StringIO(data)
   except: f=StringIO(data.encode('utf-8'))
   def _fixJSON(event):
      # функция исправляет "фичу" декодинга, Которая пытается все цифровые типы привести к decimal()
      if event[1]=='number':
         return (event[0], event[1], float(event[2]) if math.modf(event[2])[0] else int(event[2]))
      else: return event
   events=imap(_fixJSON, ijson.parse(f))
   g=common.items(events, (arrayKey+'.item' if arrayKey else 'item'))
   # g=ijson.items(f, (arrayKey+'.item' if arrayKey else 'item'))
   return g

def reprEx(obj, indent=None, toUtf8=True, sortKeys=True):
   def _fixJSON(o):
      if isinstance(o, decimal.Decimal): return str(o) #fix Decimal conversion
      if isinstance(o, (datetime.datetime, datetime.date, datetime.time)): return o.isoformat() #fix DateTime conversion
   try:
      s=json.dumps(obj, indent=indent, separators=(',',':'), ensure_ascii=False, sort_keys=sortKeys, default=_fixJSON)
   except:
      try: s=json.dumps(obj, indent=indent, separators=(',',':'), ensure_ascii=True, sort_keys=sortKeys, default=_fixJSON)
      except Exception as e:
         print '!!! JSON dump', e
         return None
   if toUtf8:
      try: s=s.encode('utf-8')
      except: pass
   return s

def numEx(val, forceFloat=False):
   #convert string to integer. if fail, convert to float. if fail return original
   if isString(val): val=val.strip()
   if forceFloat:
      try: return float(val)
      except: return val
   try: return int(val)
   except:
      try: return float(val)
      except: return val
intEx=numEx

def uLower(s):
   try: s=s.decode('utf-8').lower().encode('utf-8')
   except: s=s.lower()
   return s

def uUpper(s):
   try: s=s.decode('utf-8').upper().encode('utf-8')
   except: s=s.upper()
   return s

def strEx(val):
   if isString(val): return val
   try: return str(val)
   except:
      try: return reprEx(val)
      except: return val

def getms(r=False):
#return time and date in miliseconds(UNIXTIME) or seconds (if r==False)
   if r: return round(time.time()*1000.0, 0)
   else: return int(time.time())

def timeTo(text, to='s'):
   #convert timestamp to $to(seconds,minutes)
   tarr=text.split(':')
   if to=='s': s=int(tarr[0])*3600+int(tarr[1])*60+int(tarr[2])
   if to=='m': s=int(tarr[0])*60+int(tarr[1])+int(tarr[2])/60
   return s

def time2human(val):
   d=24*60*60*1000.0
   h=60*60*1000.0
   m=1*60*1000.0
   s=1*1000.0
   if val>d: val='%sd'%(round(val/d, 2))
   elif val>h: val='%sh'%(round(val/h, 2))
   elif val>m: val='%sm'%(round(val/m, 1))
   elif val>s: val='%ss'%(round(val/s, 1))
   else: val='%sms'%(int(val))
   return val

def dateComp(date, datewith=None, format='%d/%m/%Y %H:%M:%S'):
   #compare to dates in $format
   if(datewith==None):
      date1=datetime.datetime.now().strftime(format)
      date2=date
   else:
      date1=date
      date2=datewith
   date1=timeNum(date1, format) if not isNum(date1) else date1
   date2=timeNum(date2, format) if not isNum(date2) else date2
   dd=date1-date2
   return dd
dateDiff=dateComp

def dateIncress(wait):
   #incress date by given seconds
   if wait=='': return None
   wait=float(wait)
   s=datetime.datetime.now()+datetime.timedelta(seconds=3600*24*wait)
   return s.strftime('%d.%m.%Y')

def timeNum(text, format='%d/%m/%Y %H:%M:%S'):
   #convert string to time
   t0=datetime.datetime.strptime(text,format)
   t1=time.mktime(t0.timetuple())
   return round(t1)
#===================================
global consoleColor
consoleColor=magicDict({
   'header':'\033[95m',
   'okblue':'\033[94m',
   'okgreen':'\033[92m',
   'ok':'\033[92m',
   'warning':'\033[93m',
   'fail':'\033[91m',
   'end':'\033[0m',
   'bold':'\033[1m',
   'underline':'\033[4m',
   'clearLast':'\033[F\033[K'
})

def consoleClear():
   #clear console outpur (linux,windows)
   if sys.platform=='win32': os.system('cls')
   else: os.system('clear')

def consoleIsTerminal():
   return sys.stdout.isatty()

global console
console=magicDict({
   'clear':consoleClear,
   'inTerm':consoleIsTerminal,
   'color':consoleColor
})

#===================================
def cmd(command, path=None, enc="utf-8"):
   process=subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=path)
   out, err=process.communicate()
   out=out.decode(enc)
   err=err.decode(enc)
   retcode=process.poll()
   if retcode:
      raise ValueError("%s has returned %d - error was %s"%(' '.join(command), retcode, err))
   return out
#===================================
def cropURL(t):
   if(t[:7]=='http://'): t=t[7:]
   if(t[:8]=='https://'): t=t[8:]
   if(t[:4]=='www.'): t=t[4:]
   return t

def rebuildURL(url, cb):
   #чиним адрес, чтобы парсить адреса без scheme
   for s in ['//', 'http://', 'https://', 'ftp://']:
      if url.startswith(s): break
   else: url='//'+url if(url.startswith('/') or '.' in strGet(url, '', '/')) else '///'+url
   #парсим
   scheme, netloc, path, query, fragment=urlsplit(url)
   if 'netloc' in cb:
      netloc=cb['netloc'](netloc) if isFunction(cb['netloc']) else cb['netloc']
   if 'path' in cb:
      path=cb['path'](path) if isFunction(cb['path']) else cb['path']
   if 'scheme' in cb:
      scheme=cb['scheme'](scheme) if isFunction(cb['scheme']) else cb['scheme']
   if 'fragment' in cb:
      if isFunction(cb['fragment']):
         fragment=parse_qs(fragment)
         tArr1={}
         for k, v in fragment.iteritems():
            if isFunction(cb['fragment']): s=cb['fragment'](k, v)
            elif isDict(cb['fragment']): s=oGet(cb['fragment'], k, v)
            else: s=cb['fragment']
            if s is not False: tArr1[k]=s
         try: fragment=urlencode(tArr1, doseq=True)
         except: fragment=''
      else: fragment=cb['fragment']
   if 'query' in cb:
      if isFunction(cb['query']):
         query=parse_qs(query)
         tArr1={}
         for k, v in query.iteritems():
            if isFunction(cb['query']): s=cb['query'](k, v)
            elif isDict(cb['query']): s=oGet(cb['query'], k, v)
            else: s=cb['query']
            if s is not False: tArr1[k]=s
         try: query=urlencode(tArr1, doseq=True)
         except: query=''
      else: query=cb['query']
   return urlunsplit((scheme, netloc, path, query, fragment))
#===================================
def sha1(text):
   #wrapper for sha1
   try: c=hashlib.sha1(text)
   except UnicodeEncodeError: c=hashlib.sha1(strUniDecode(text))
   return c.hexdigest()

def sha256(text):
   #wrapper for sha256
   try: c=hashlib.sha256(text)
   except UnicodeEncodeError: c=hashlib.sha256(strUniDecode(text))
   return c.hexdigest()

def md5(text):
   #wrapper for sha1
   try: c=hashlib.md5(text)
   except UnicodeEncodeError: c=hashlib.md5(strUniDecode(text))
   return c.hexdigest()
#===================================
def pathList(path, fullPath=True, alsoFiles=True, alsoDirs=False):
   res=[]
   for f in os.listdir(path):
      fp=os.path.join(path, f)
      if not alsoDirs and not os.path.isfile(fp): continue
      if not alsoFiles and os.path.isfile(fp): continue
      res.append(fp if fullPath else f)
   return res

def fileGet(fName, method='r'):
   #get content from file,using $method and if file is ZIP, read file $method in this archive
   fName=fName.encode('cp1251')
   if not os.path.isfile(fName): return None
   if zipfile.is_zipfile(fName):
      c=zipfile.ZipFile(fName, method)
      try:
         s=c.read(method)
      except KeyError:
         error('reading zip file '+fName+':'+method)
      c.close()
   else:
      try:
         with open(fName, method) as f: s=f.read()
      except: return None
   return s

def fileAppend(fName, text, mode='a'):
   # if not isString(text): text=repr(text)
   # with open(fName,mode) as f: f.write(text)
   return fileWrite(fName, text, mode)

def fileWrite(fName, text, mode='w'):
   """ 'a' - в конец файла / 'w' - перезапись файла """
   if not isString(text): text=repr(text)
   with open(fName,mode) as f: f.write(text)

def error(text,exit=True,pause=False):
   print 'ERROR: '+text
   if pause: raw_input()
   if exit: sys.exit(0)

def grouper(n,obj,fill=None):
   #group items by n (ABCDEFG --> ABC DEF Gxx if n=3)
   args=[iter(obj)]*n
   return izip_longest(fill=fill,*args)
#===================================
def strIsUpBegin(str):
#проверяет, является ли первая найденная буква слова заглавной. игнорирует остальные символы в начале слова
   return bool(sum([int(s.isupper()) for s in str if s in uLetters]))

def strGet(text, pref='', suf='', index=0, default='', returnOnlyStr=True):
   #return pattern by format pref+pattenr+suf
   if(text==''):
      if returnOnlyStr: return default
      else: return -1, -1, default
   text1=text.lower()
   pref=pref.lower()
   suf=suf.lower()
   if pref!='': i1=text1.find(pref,index)
   else: i1=index
   if i1==-1:
      if returnOnlyStr: return default
      else: return -1, -1, default
   if suf!='': i2=text1.find(suf,i1+len(pref))
   else: i2=len(text1)
   if i2==-1:
      if returnOnlyStr: return default
      else: return i1, -1, default
   s=text[i1+len(pref):i2]
   if returnOnlyStr: return s
   else: return i1+len(pref), i2, s
###str.get=strGet

def str2dict(text, sep1='=', sep2=' '):
   #create dict{key:val} from string"key(sep1)val(sep2)"
   tArr1=text.split(sep2)
   tArr2={}
   for s in tArr1:
      if not s: continue
      s1=strGet(s, '', sep1, default=s)
      s2=strGet(s, sep1, default='')
      if s1: tArr2[s1]=s2
   return tArr2
###str.toDict=strToDict

def strUniDecode(text, alsoU=True):
   #decode unicode's things for russian,use map
   try:text = text.encode('utf-8').replace('°', ' ')
   except: pass
   if alsoU:
      try: text=str(text).replace('\\u0075', 'u').replace('\\u0055', 'U')
      except: pass
   try:
      for f, to in ucodes.iteritems(): text=str(text).replace(f, to)
   except: pass
   return text #.decode('unicode_escape')C###str.uniDecode=strUniDecode

def strUniEncode(text, alsoU=True):
   #encode unicode's things for russian,use map
   if alsoU:
      try: text=str(text).replace('u', '\\u0075').replace('U', '\\u0055')
      except: pass
   try:
      for to,f in ucodes.iteritems():
         text=text.replace(f, to)
   except: pass
   return text###str.uniEncode=strUniEncode

def print_r(arr, pref=''): #принтит обьект
   try:
      from decimal import Decimal
      if isDict(arr):
         for k in arr.iterkeys():
            if isDict(arr[k]):
               for kk in arr[k].iterkeys():
                  if isinstance(arr[k][kk], (datetime.date, datetime.datetime)): arr[k][kk]=str(arr[k][kk])
                  if isinstance(arr[k][kk], (int, float, long, Decimal)): arr[k][kk]=str(arr[k][kk])
            else:
               if isinstance(arr[k], (datetime.date, datetime.datetime)): arr[k]=str(arr[k])
               if isinstance(arr[k], (int, float, long, Decimal)): arr[k]=str(arr[k])
      print pref, strUniDecode(reprEx(arr,2))
   except:
      print 'ERROR in print_r'

def print_rd(arr,pref=''): #принтит и делает die
   # print '\n!!! (PRD) !!!\n'
   print_r(arr, pref)
   sys.exit(0)

def strEscDecode(text):
   #decode esc(\n,\t) things
   return repr(text).decode('string_escape')
###str.escDecode=strEscDecode

def strSplitEX(text,s1=',', s2=None, totype=None, strip=False):
   #split string to 2 dimensions array and optional convert elements to $type
   if text==None: return []
   if not isString(text): text=strEx(text)
   tArr1=text.split(s1)
   if strip: tArr1=[s.strip() for s in tArr1]
   if s2!=None:
      for i in xrange(len(tArr1)):
         tArr2=tArr1[i].split(s2)
         if strip: tArr2=[s.strip() for s in tArr2]
         if len(tArr2)>1: tArr1[i]=tArr2
   if totype=='num': tArr1=arrToNum(tArr1)
   return tArr1
###str.splitEX=strSplitEX
#===================================
def arrFind(arr, item, default=-1):
   """аналог str.find() для массивов"""
   try: return arr.index(item)
   except: return default

def arrDelta(arr, key=None):
#находим дельту между двумя каждыми соседними элементами
   #элементы должны быть числами
   dArr=[]
   tArr=sorted(arr, key=key, reverse=True)
   for i in xrange(1,len(tArr)):
      v1=float(key(tArr[i-1]) if key else tArr[i-1])
      v2=float(key(tArr[i]) if key else tArr[i])
      dArr.append(v1-v2)
   return dArr
###list.delta=arrDelta

def arrEjectionClean3(arr, delicacy=1.03, returnEjections=False, returnIndex=False, sortKey=None, allowSort=True):
#чистит цифровую выборку от выбросов, используя робастный подход по соседним значениям
   arrMap=[i for i in xrange(len(arr))]
   if(allowSort): #в нормальных условия метод работает корректно только для отсортированных массивов
      arrMap=sorted(arrMap, key=(lambda x: sortKey(arr[x]) if sortKey else arr[x]), reverse=False)
   out=[]
   last=None
   for i in arrMap:
      e=arr[i]
      if last==None and e==0:
         if not returnEjections: out.append(i)
         continue
      elif last!=None and (e-last>float(delicacy)*last):
         if returnEjections: out.append(i)
         continue
      if not returnEjections: out.append(i)
      last=e
   if returnIndex: out=[i for i in xrange(len(arr)) if i in out]
   else: out=[arr[i] for i in xrange(len(arr)) if i in out]
   return out

def arrEjectionClean(arr, allowSort=True, sortKey=None, robustMultiplier=0.9, returnEjections=False):
#чистит цифровую выборку от выбросов, используя робастный подход по соседним значениям
   return arrEjectionClean3(arr=arr, allowSort=allowSort, returnEjections=returnEjections, sortKey=sortKey, delicacy=robustMultiplier, returnIndex=False)

def arrMedian(arr, arrMap=None):
   if not len(arr): return 0
   elif len(arr)==1: return arr[0]
   if not arrMap:
      arrMap=sorted(range(len(arr)), key=lambda i:arr[i], reverse=False)
   if len(arrMap)%2:
      median=arr[arrMap[len(arrMap)/2]]
   else:
      median=(arr[arrMap[(len(arrMap)-1)/2]]+arr[arrMap[(len(arrMap)-1)/2+1]])/2.0
   return median

def arrQuartiles(arr, arrMap=None, method=1):
   if not len(arr): return 0
   elif len(arr)==1: return arr[0]
   if not arrMap:
      arrMap=sorted(range(len(arr)), key=lambda i:arr[i], reverse=False)
   median=arrMedian(arr, arrMap)
   def getHalve(isLow=True, includeM=False):
      tArr=[]
      for i in arrMap:
         if isLow and (arr[i]<=median if includeM else arr[i]<median): tArr.append(arr[i])
         if not isLow and (arr[i]>=median if includeM else arr[i]>median): tArr.append(arr[i])
      tArrMap=range(len(tArr))
      return tArr, tArrMap
   if method in [1, 2]: #methods "1-Var Stats" and "Tukey's hinges"
      tHalveL, tHalveL_arrMap=getHalve(True, method==2)
      tHalveH, tHalveH_arrMap=getHalve(False, method==2)
      qL=arrMedian(tHalveL, tHalveL_arrMap)
      qH=arrMedian(tHalveH, tHalveH_arrMap)
   elif method==3:
      tHalveL1, tHalveL1_arrMap=getHalve(True, False)
      tHalveH1, tHalveH1_arrMap=getHalve(False, False)
      qL1=arrMedian(tHalveL1, tHalveL1_arrMap)
      qH1=arrMedian(tHalveH1, tHalveH1_arrMap)
      tHalveL2, tHalveL2_arrMap=getHalve(True, True)
      tHalveH2, tHalveH2_arrMap=getHalve(False, True)
      qL2=arrMedian(tHalveL2, tHalveL2_arrMap)
      qH2=arrMedian(tHalveH2, tHalveH2_arrMap)
      qL=(qL1+qL2)/2.0
      qH=(qH1+qH2)/2.0
   return qL, median, qH

def arrTrimean(arr, arrMap=None):
   """
    >>> trimean([1, 1, 3, 5, 7, 9, 10, 14, 18])
    6.75
    >>> trimean([0, 1, 2, 3, 4, 5, 6, 7, 8])
    4.0
   """
   if not len(arr): return 0
   elif len(arr)==1: return arr[0]
   if not arrMap:
      arrMap=sorted(range(len(arr)), key=lambda i:arr[i], reverse=False)
   q1, m, q3=arrQuartiles(arr, arrMap, method=2)
   trimean=(q1+2.0*m+q3)/4.0
   return trimean

def arrMode(arr, rank=0, returnIndex=False):
   arrMap={}
   for i, v in enumerate(arr):
      if v not in arrMap: arrMap[v]=[]
      arrMap[v].append(i)
   kMap=arrMap.keys()
   if rank>=len(kMap):
      return [] if returnIndex else None
   kMap=sorted(kMap, key=lambda s: len(arrMap[s]), reverse=True)
   k=kMap[rank]
   return arrMap[k] if returnIndex else k
   # arrMap=sorted(set(arr), key=arr.count, reverse=True)
   # i=arrMap[rank] if rank<len(arrMap) else None
   # return i if returnIndex else arr[i]

def arrEjectionClean2(arr, delicacy=0.51, returnEjections=False, returnIndex=False, useTrimean=False):
#чистит цифровую выборку от выбросов, используя робастный подход по медиане или тримеане
   out=[]
   if useTrimean: median=arrTrimean(arr)
   else: median=arrMedian(arr)
   medianM=abs(float(delicacy)*median)
   for i in range(len(arr)):
      if abs(median-arr[i])>medianM:
         if not returnEjections: continue
         else:
            out.append(i if returnIndex else arr[i])
            continue
      if not returnEjections: out.append(i if returnIndex else arr[i])
   return out

def arrAverage(arr, robust=False):
   if robust: arr=arrEjectionClean2(arr)
   if not len(arr): return 0 #защита от деления на ноль
   return sum(arr)/float(len(arr))

def arrMax(arr, key=None, returnIndex=False):
   """позволяет использовать key при поиске максимума"""
   if not len(arr): return 0 if not returnIndex else -1
   elif len(arr)==1: return arr[0] if not returnIndex else 0
   if key: arr=[key(s) for s in arr]
   if not returnIndex:
      try: return max(arr)
      except: return None
   else:
      try: return arrFind(arr, max(arr))
      except: -1

def arrMin(arr, key=None, returnIndex=False):
   """позволяет использовать key при поиске максимума"""
   if not len(arr): return 0 if not returnIndex else -1
   elif len(arr)==1: return arr[0] if not returnIndex else 0
   if key: arr=[key(s) for s in arr]
   if not returnIndex:
      try: return min(arr)
      except: return None
   else:
      try: return arrFind(arr, min(arr))
      except: -1

def arrAdd(arr, vals):
   """добавляет в многомерный массив 'arr' значения из многомерного массива 'vals' синхронно. если значения массива 'vals' сами являютсю массивами (их длинна дожна быть одинаковой) они также добавятся синхронно"""
   if len(vals)!=len(arr): return None
   tarr1=arr[:]
   l0=None
   for i in xrange(len(vals)):
      if isArray(vals[i]):
         if l0==None: l0=len(vals[i])
         elif l0!=len(vals[i]): return None
         l0=len(vals[i])
         for j in xrange(l0): tarr1[i].append(vals[i][j])
      elif l0!=None: return None
      else: tarr1[i].append(vals[i])
   return tarr1
###list.add=arrAdd

def arrCreate(s1=2, s2=2, val=None):
   #create 2 dimensions array, filled with $val
   tArr=[]
   for i in xrange(s1):
      if s2 in [0, None]:
         tArr.append(val)
      else:
         tArr.append([])
         for j in xrange(s2):
            tArr[i].append(val)
   return tArr

def arrToDict(arr,keys):
   #convert array and $keys to dict
   tarr0={}
   for i in xrange(len(keys)): tarr0[keys[i]]=arr[i]
   return tarr0
###list.toDict=arrToDict

def arrJoin(arr,sep1=',',sep2='.',fillnull=True):
   #join 2 dimensoins array
   s=''
   for arri in arr:
      if isArray(arri): s+=arrJoin(arri,sep2)+sep1
      else:
         if fillnull and arri==None: s+=sep1
         else: s+=str(arri)+sep1
   return s[0:len(s)-1] if len(s)>0 else ''
###list.join=arrJoin

def arrClean(arr, nulls=['', None]):
   #clear array from empty elements
   tarr=[s for s in arr if s not in nulls]
   return tarr
###list.clean=arrClean

def arrToNum(arr, clean=False, sub=False):
   #convert elements to num. if $sub==true,convert subarrays too.
   if isArray(arr)==False: return arr
   if len(arr)==0: return []
   tarr=[]
   for i in xrange(len(arr)):
      if sub and isArray(arr[i]): tarr.append(arrToNum(arr[i],clean,False))
      else:
         s=numEx(arr[i])
         if isNum(s) or not clean: tarr.append(s)
   return tarr
###list.toNum=arrToNum

def oGet(o, key, default=None):
   #get val by key from object(list,dict), and default if key not exist
   try: return o[key]
   except: return default
arrGet=oGet
###list.get=arrGet

def arrUnique(arr, key=None):
   #unique elements of array
   if not(arr): return []
   # tarr={}
   # result=[]
   # for e in arr:
   #    if key: eKey=key(e)
   #    else: eKey=e
   #    if eKey in tarr: continue
   #    tarr[eKey]=0
   #    result.append(e)
   # return result
   tArr1=arr
   if key: tArr1=[key(s) for s in tArr1]
   tArr1=set(tArr1)
   tArr1=list(tArr1)
   return tArr1

###list.unique=arrUnique

def dictToArr(arr, keys=None):
   #convert dict to array and sort items by $keys
   if not keys: keys=arr.keys()
   tArr0=[arr[i] for i in keys]
   return tArr0
###dict.toArray=dictToArr
#===================================
def sendmail(p={}):
   p=magicDict(p)
   import smtplib, email
   from email.MIMEText import MIMEText
   from email.MIMEBase import MIMEBase
   from email.MIMEImage import MIMEImage
   from email.mime.audio import MIMEAudio
   from email.mime.application import MIMEApplication
   from email import Encoders
   msg=email.MIMEMultipart.MIMEMultipart()
   msg['From']=oGet(p, 'from', oGet(p, 'login', oGet(p, 'user', '')))
   # msg['To']=email.Utils.COMMASPACE.join(regExp_splitEmail.split(p.to) if isString(p.to) else p.to)
   # msg['To']= p.to.split(',') if isString(p.to) else p.to
   if isString(p.to):
      p.to=p.to.split(',')
   # print_rd(msg['To'])
   msg['Subject']=oGet(p, 'subject', oGet(p, 'title', ''))
   #attach body
   # msg.attach(MIMEText(oGet(p, 'body', oGet(p, 'text', '')), oGet(p, 'mime', 'plain'), "utf-8"))
   msg.attach(MIMEText(oGet(p, 'body', oGet(p, 'text', '')), oGet(p, 'mime', 'html'), "utf-8"))
   #attach other
   #http://stackoverflow.com/a/11921241/5360266 https://gist.github.com/vjo/4119185
   typeMap={
      'img':MIMEImage, 'image':MIMEImage, 'png':{'o':MIMEImage, 'm':'png'}, 'jpg':{'o':MIMEImage, 'm':'jpg'}, 'jpeg':{'o':MIMEImage, 'm':'jpeg'},
      'audio':MIMEAudio, 'sound':MIMEAudio, 'pdf':MIMEApplication, 'mp3':{'o':MIMEAudio, 'm':'mp3'}, 'wav':{'o':MIMEAudio, 'm':'wav'},
      'pdf':{'o':MIMEApplication, 'm':'pdf'},
      'xlsx':{'o':MIMEApplication,'m':'xlsx'}
   }
   cids=[]
   for o in oGet(p,'xlsx',[]):
      part = MIMEBase('application', "octet-stream")
      part.set_payload(open(o['path'], "rb").read())
      from email import encoders
      encoders.encode_base64(part)
      part.add_header('Content-Disposition', 'attachment; filename='+o['name'])
      msg.attach(part)
   for o in oGet(p, 'attach', []):
      cid=''
      name=''
      if isDict(o):
         oo=oGet(typeMap, oGet(o, 'type', ''), MIMEApplication)
         a=oo['o'](o['data'], oo['m']) if isDict(oo) else oo(o['data'])
         cid=oGet(o, 'cid', randomEx(65536, cids, '<', '>'))
         name=oGet(o, 'name', '')
      else: #binary data
         a=MIMEApplication(o)
         cid=randomEx(65536, cids, '<', '>')
      #if no cid, client like MAil.app (only one?) don't show the attachment
      if not isString(cid): cid='<%s>'%cid
      if not cid.startswith('<'): cid='<%s'%cid
      if not cid.endswith('>'): cid='%s>'%cid
      cids.append(cid)
      a.add_header('Content-ID', cid)
      if name:
         a.add_header('Content-Disposition', 'attachment', filename=name)
         a.add_header('Content-Disposition', 'inline', filename=name)
      msg.attach(a)
   #send
   try:
      isSSL=oGet(p, 'isSSL', oGet(p, 'ssl', False))
      if isSSL: server=smtplib.SMTP_SSL(p.server, oGet(p, 'port', 465))
      else: server=smtplib.SMTP(p.server, oGet(p, 'port', 587))
      server.ehlo()
      if not isSSL:
         server.starttls()
         server.ehlo()
      server.login(oGet(p, 'login', oGet(p, 'user', '')), oGet(p, 'password', oGet(p, 'passwd', '')))
      server.sendmail(msg['From'], p.to, msg.as_string())
      server.close()
      return True
   except Exception as e: return e

def gmailSend(login, password, to, text, subject='', attach=[]):
   return sendmail({'isSSL':True, 'server':'smtp.gmail.com', 'login':login, 'password':password, 'to':to, 'subject':subject, 'text':text, 'attach':attach})

def yaSend(login, password, to, text, subject='', attach=[]):
   return sendmail({'isSSL':True, 'server':'smtp.yandex.ru', 'login':login, 'password':password, 'to':to, 'subject':subject, 'text':text, 'attach':attach})

global gmail
gmail=magicDict({'send':gmailSend})
#===================================
def intersectWord(s, arr):
   s=s.lower()
   arr=[a.lower() for a in arr]
   out=difflib.get_close_matches(s, arr)
   return out

def wordImpulse(wordE, word, returnMax=False):
#находим рейтинг схождения двух символьных последовательностей
   #!нужно обрабатывать окончания
   if not len(word) or not len(wordE): return None
   #определяем все исключающие последовательность, одинаковые для обоис псоледовательностей
   iParams={}
   for i1 in xrange(len(wordE)):
      iParams[i1]={'index':None, 'len':None, 'indexE':i1}
      iArr=xrange(len(word))
      for m in xrange(len(wordE)-i1+1):
         iArr2=[i2 for i2 in iArr if wordE[i1:i1+m+1]==word[i2:i2+m+1]]
         if not len(iArr2): break
         iArr=iArr2
      iParams[i1]['index']=iArr[0]
      iParams[i1]['len']=m
   #сама длинная является опорной
   best=iParams[sorted(range(len(wordE)), key=lambda x:(iParams[x]['len'],len(word)-iParams[x]['index']), reverse=True)[0]]
   rate={0.9:best['len']+1, 0.7:0, 0.3:0}
   if best['index']==0: rate[0.9]+=1
   elif best['index']==1: rate[0.7]+=1
   elif best['index']>=2: rate[0.3]+=1
   #далее проверяем оставшиеся символы
   i1=best['index']+best['len']
   i2=best['indexE']+best['len']
   while i2<len(wordE)-best['indexE']-best['len']:
      rate[0.9]+=0 if iParams[i2]['len']<=1 else iParams[i2]['len']
      if iParams[i2]['index']-i1==0: rate[0.9]+=1
      elif iParams[i2]['index']-i1==1: rate[0.7]+=1
      elif iParams[i2]['index']-i1>=2: rate[0.3]+=1
      i1=iParams[i2]['len']+iParams[i2]['index'] if iParams[i2]['len']>0 else 1+iParams[i2]['index']
      i2=iParams[i2]['len']+iParams[i2]['indexE'] if iParams[i2]['len']>0 else 1+iParams[i2]['indexE']
   rating=2**sum([k*v for k,v in rate.items()])
   maxR=2**(len(wordE)+1)
   if not returnMax: return rating
   else: return rating, maxR

def wordCompare(wordE=None, word=None, onlyReturnMaxLen=False, nearMap=None, caseSensitive=False):
# сравнивает 2 строки с учетом таблици замен
   nearMap=nearMap if isDict(nearMap) else {u'сч=щ':0.3 ,u'т=д':0.3, u'ъ=ь':0.1, u'г=к':0.3}
   maxN=0
   if nearMap:
      #автоматически создаем обратные соответствия, нужны для ускорения поиска
      nearMap.update(dict([('%s=%s'%tuple(k.split('=')[::-1]), v) for k,v in nearMap.items()]))
      maxN=max([max([len(s) for s in k.split('=')]) for k in nearMap.keys()])
   if onlyReturnMaxLen: return maxN
   if not caseSensitive:
      wordE=wordE.lower()
      word=word.lower()
   rating=0
   maxRating=0
   l1=1
   l2=1
   while l1<=len(wordE):
      w1=wordE[:l1]
      w2=word[:l2]
      # print w1,w2
      maxRating+=1
      if w1[-1]==w2[-1]: rating+=1 #прямое сравнение
      elif maxN>0:
         #сравнение через таблицу замен
         for tl1 in range(maxN+1)[::-1]:
            if l1-1+tl1>len(wordE): continue
            for tl2 in range(maxN+1)[::-1]:
               if l2-1+tl2>len(word): continue
               s=u'%s=%s'%(wordE[l1-1:l1-1+tl1], word[l2-1:l2-1+tl2])
               # print '+'*7, s
               if s not in nearMap: continue # or wordE[:l1-1]!=word[:l2-1]
               # print '-'*7, wordE[:l1-1],word[:l2-1]
               # print '!'*10
               rating+=(1-nearMap[s]) #преобразуем штраф в баллы
               break
            if tl2>0 and tl1>0:
               l1+=(tl1-1)
               l2+=(tl2-1)
               break
         if tl1==0 or tl2==0: return False, rating, maxRating
      else: return False, rating, maxRating
      l1+=1
      if l2<=len(word): l2+=1
   return True, rating, maxRating

def wordMatchPart(wordE, word, nearMap=None, partParamsExternal={}, caseSensitive=False):
   partParams=partParamsExternal or {}
   # благодаря функции сравнения тпепрь нужно просто пройтись по всем кусочкам
   i1=0
   l1=1
   l2=1
   i2=0
   rating=0
   lastOk=None
   while i1<len(wordE):
      w1=wordE[i1:i1+l1]
      w2=word[i2:i2+l2]
      # print w1, w2
      isOk, r, mr=wordCompare(w1, w2, nearMap=nearMap, caseSensitive=caseSensitive)
      if isOk:
         #совпали, берем на букву больше
         l1+=1
         l2+=1
         rating=r
         lastOk=magicDict({'index1':i1, 'index2':i2, 'len1':l1-1, 'len2':l2-1, 'text1':w1, 'text2':w2, 'rating':rating, 'maxRating':mr})
         # print '   +++'
         if (i1+l1>len(wordE)) and (i2+l2>len(word)):
            try: lastOk
            except: break
            if lastOk and lastOk.rating: partParams['%s:%s'%(lastOk.index1,lastOk.len1)]=lastOk
            break
      else:
         if i2+l2<len(word): l2+=1
         elif i2+1<len(word):
            l2=l1
            i2+=1
         else:
            try:
               if lastOk and lastOk.rating: partParams['%s:%s'%(lastOk.index1,lastOk.len1)]=lastOk
            except: pass
            if i1+l1<len(wordE):
               l1+=1
               i2=0
               l2=1
            elif i1+1<len(wordE):
               i1+=1
               l1=1
               i2=0
               l2=1
            else: break
            rating=0
            lastOk=None
   if not len(partParams.values()):
      return magicDict({'index1':0, 'index2':0, 'len1':0, 'len2':0, 'text1':'', 'text2':'', 'rating':0, 'maxRating':0})
   elif len(partParams.values())==1: return partParams.values()[0]
   else: return sorted(partParams.values(), key=lambda x:x['rating'])[-1]

def wordImpulse2(wordE, word, returnMax=False, nearMap=None, caseSensitive=False):
   #находим импульс, необходимый для превращения одного слова в другое
   partParams={}
   bestPart=wordMatchPart(wordE, word, nearMap=nearMap, partParamsExternal=partParams, caseSensitive=caseSensitive)
   #!какаято хрень с форматом
   print_r(bestPart)
   #найдена максимальная последовательность
   finalRating=0.0
   leftPartE=wordE[:int(bestPart.index1)][::-1] #! Здесь было ':'
   # leftPart=word[:int(bestPart.index2)][::-1]
   rightPartE=wordE[int(bestPart.index1)+int(bestPart.len1):]
   # rightPart=word[int(bestPart.index2)+int(bestPart.len2):]
   #ищем совпадения в оставшихся частях слов
   # print leftPartE, leftPart, rightPartE, rightPart
   i1=0
   l1=1
   lastOk=False
   while i1<len(rightPartE):
      # print '%s:%s'%(i1+int(bestPart['index1'])+int(bestPart['len1']),l1)
      if '%s:%s'%(i1+int(bestPart.index1)+int(bestPart.len1),l1) not in partParams:
         if l1>=wordCompare(onlyReturnMaxLen=True): #длинна проверяемого сегмента меньше максимальной в таблице замен
            if l1-1>0 and lastOk:
               #проверяемый сегмент не прошел проверку, однако прошел ее ранее при меньшей длинне
               print '!', wordE[i1+int(bestPart.index1)+int(bestPart.len1):i1+int(bestPart.index1)+int(bestPart.len1)+l1-1]
               finalRating+=partParams['%s:%s'%(i1+int(bestPart.index1)+int(bestPart.len1),l1-1)].rating
            #к следующему сегменту
            i1+=1
            l1=1
            lastOk=False
         else: l1+=1 #увеличиваем длинну проверяемого сегмента
      else: #сегмент прошел проверку
         lastOk=True
         l1+=1
   """
   нужно переписать основу подсчета рейтинга.
   он должен считать не похожесть, а расличия.
   найденная лучшая часть это 0+коэффициент_ошибок_по_таблице_замен
   дальше влево от нее за каждую
   """
   return finalRating
   # print_r(partParams)
#===================================
def levenshtein2(a, b):
#find the Levenshtein's distance
   #! Алгоритм из википедии, нужно проверить
   n, m = len(a), len(b)
   if n > m:
      # Make sure n <= m, to use O(min(n,m)) space
      a, b = b, a
      n, m = m, n
   current_row = range(n+1) # Keep current and previous row, not entire matrix
   for i in range(1, m+1):
      previous_row, current_row = current_row, [i]+[0]*n
      for j in range(1,n+1):
         add, delete, change = previous_row[j]+1, current_row[j-1]+1, previous_row[j-1]
         if a[j-1] != b[i-1]: change += 1
         current_row[j] = min(add, delete, change)
   return current_row[n]

def levenshtein(s1, s2, ignoreCaseAndStrip=True):
#find the Levenshtein's distance
   #! Пока используется упрощенная имплементация из стандартного модуля
   if ignoreCaseAndStrip:
      s1=s1.lower().strip()
      s2=s2.lower().strip()
   rate=1-difflib.SequenceMatcher(None, s1, s2).ratio()
   return rate
#===================================

if(__name__=='__main__'):
   text=' {asd}/{rwqeqw}/{zcxc}'
   i1, i2, s=strGet(text, '/', '/', index=0, returnOnlyStr=False)
   print i1, i2, s, text[i1:i2]
   sys.exit(0)
   tArr1=[0, 1, 2, 3, 4, 5, 6, 7, 8]
   print arrTrimean(tArr1), sys.exit(0)
   # tArr1=[6, 7, 15, 36, 39, 40, 41, 42, 43, 47, 49]
   # print arrQuartiles(tArr1, method=1), arrQuartiles(tArr1, method=2), arrQuartiles(tArr1, method=3), sys.exit(0)
   # print gmail.send('byaka.life@gmail.com', '35921514', 'byaka.life@gmail.com', 'this is a test message', 'Test'), sys.exit(0)
   # print arrEjectionClean2([10, 20, 0, 0.11, 1.12, 0.22, 0.31, 1.24, 0.51, 0.72], returnIndex=False, returnEjections=False, useTrimean=True), sys.exit(0)
   # print intersectWord('b-common__list_font_bold', ['prof-on-board__road-icon_type_join'])
   # print wordMatchPart('b-common__list_font_bold', 'prof-on-board__road-icon_type_join', nearMap={}, caseSensitive=True)
   sys.exit(0)
   # print wordImpulse2(u'щет', u'счед')
   # print wordImpulse2(u'подьезжал', u'съездил')
