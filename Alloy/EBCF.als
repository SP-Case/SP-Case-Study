module SPtest/BCF/BCF

open SPtest/BCF/Log
open SPtest/BCF/Stop
open SPtest/BCF/AccountM
open SPtest/BCF/DonateM

sig RCReturn extends ReturnWithLog {
	ure:UserReturn
}

sig WDLReturn extends ReturnWithLog {
	wre:WDReturn
}

sig SPLReturn extends ReturnWithLog {
	eure:EUReturn
}

sig DLReturn extends ReturnWithLog {
	dere:DEReturn
}
	
//替换变量(3)
//替换操作(1)
//删除公理(2)
//删除if(2)
pred rechargeWithLog[u,n:Int, dbu:UserDB, dbl:LogDB, s:Status,
					 re:RCReturn] {
	s.value = true => {		//替换常量(1)
		addBalance[u,n,dbu,re.ure]
		log[u,RC,dbl,re.lre]		//替换常量(1)
	}
	s.value = false => {
		re.ure.user = null	
		re.ure.udb = dbu
		re.lre.ldb = dbl
	}
}

run rechargeWithLog for 4

pred withdrawWithLog[u,t,n:Int, rid:RID, l:Limit, dbr:RDB, dbu:UserDB, dbl:LogDB, s:Status,
					 re:WDLReturn] {
	s.value = true => {
		withdraw[u,t,n,rid,l,dbr,dbu,re.wre]
		log[u,WD,dbl,re.lre]
	}
	s.value = false => {
		re.wre.ure.user = null	
		re.wre.ure.udb = dbu
		re.lre.ldb = dbl
		re.wre.rre.rdb = dbr
	}
}

run withdrawWithLog for 4

pred stopAndPayWithLog[u,i:Int, dbe:EventDB, dbu:UserDB, dbl:LogDB, s:Status,
					   re:SPLReturn] {
	s.value = true => {
		stopAndPay[u,i,dbe,dbu,re.eure]
		log[u,SE,dbl,re.lre]
	}
	s.value = false => {
		re.eure.ure.user = null
		re.eure.ere.e = null
		re.eure.ure.udb = dbu
		re.eure.ere.edb = dbe
		re.lre.ldb = dbl
	}
}

run stopAndPayWithLog for 4

pred donateWithLog[ui,ei,n:Int, dbd:DonateDB, dbe:EventDB, dbu:UserDB, dbl:LogDB, s:Status,
				   re:DLReturn] {
	s.value = true => {
		donate[ui,ei,n,dbd,dbe,dbu,re.dere]
		log[ui,DN,dbl,re.lre]
	}
	s.value = false => {
		re.dere.dre.d = null
		re.dere.ere.e = null
		re.dere.ure.udb = dbu
		re.dere.ere.edb = dbe
		re.lre.ldb = dbl	
	}
}

run donateWithLog for 4

//mono(22)
check rechargeWithLog1_4 {
	//余额增加
	//log * 2
	//s.value = false
	all u,n:Int, dbu:UserDB, dbl:LogDB, s:Status,
		re:RCReturn|
	rechargeWithLog[u,n,dbu,dbl,s,re] => {
		let ou = u.(dbu.datas) {
			s.value = true && re.ure.user != null => re.ure.user.balance = add[ou.balance, n]
			s.value = true => re.lre.log.uid = u
			s.value = true => re.lre.log.op = RC
			s.value = false => re.ure.user = null
		}
	}
}for 20

check withdrawWithLog1_5 {
	//提现成功:余额变化
	//提现失败:余额不足
	//log * 2
	//s.value = false
	all u,t,n:Int, rid:RID, l:Limit, dbr:RDB, dbu:UserDB, dbl:LogDB, s:Status,
		re:WDLReturn |
	withdrawWithLog[u,t,n,rid,l,dbr,dbu,dbl,s,re] => {
		let ou = u.(dbu.datas) {
			no dbr.datas && s.value = true && ou.balance >= n => re.wre.ure.user.balance = sub[ou.balance, n]
			ou.balance < n => re.wre.ure.user = null
			s.value = true => re.lre.log.uid = u
			s.value = true => re.lre.log.op = WD
			s.value = false => re.wre.ure.user = null
		}
	}
}for 20

check stopAndPayWithLog1_7 {
	//中止成功:状态变化/余额变化
	//中止失败:已中止/非发起者
	//log * 2
	//s.value = false
	all u,i:Int, dbe:EventDB, dbu:UserDB, dbl:LogDB, s:Status,
		re:SPLReturn |
	stopAndPayWithLog[u,i,dbe,dbu,dbl,s,re] => {
		let ou = u.(dbu.datas), ev = i.(dbe.datas) {
			s.value = true && ev.uid = u && ev.status = true => re.eure.ere.e.status = false
			re.eure.ure.user != null => re.eure.ure.user.balance = add[ou.balance, re.eure.ere.e.total]
			ev.status = false => re.eure.ere.e = null
			ev.uid != u => re.eure.ere.e = null
			s.value = true => re.lre.log.uid = u
			s.value = true => re.lre.log.op = SE
			s.value = false => re.eure.ere.edb = dbe
		}
	}
}for 20

check donateWithLog1_6 {
	//捐赠成功(项目金额增加)
	//捐赠失败:余额不足/已中止
	//log * 2
	//s.value = false
	all ui,ei,n:Int, dbd:DonateDB, dbe:EventDB, dbu:UserDB, dbl:LogDB, s:Status,
	    re:DLReturn |
	donateWithLog[ui,ei,n,dbd,dbe,dbu,dbl,s,re] => {
		let ou = ui.(dbu.datas), ev = ei.(dbe.datas) {
			s.value = true && ou.balance >= n && ev.status = true => re.dere.ere.e.total = add[ev.total, n]
			ou.balance < n => re.dere.ere.edb = dbe
			ev.status = false => re.dere.ere.e = null
			s.value = true => re.lre.log.uid = ui
			s.value = true => re.lre.log.op = DN
			s.value = false => re.dere.ere.edb = dbe
		}
	}
}for 20

//seq(26)
//账户
//1.查询-充值-查询-提现-查询(6:数值变化-提现数量是否超过余额，日志变化）
check assert1_6 {
	all u,t,n1,n2:Int, rid:RID, l:Limit, dbr:RDB, dbu:UserDB, dbl:LogDB, s:Status,
		u1,u2,u3:AbsData, re1:RCReturn, re2:WDLReturn |
	getBalance[u,dbu,u1] &&
	rechargeWithLog[u,n1,dbu,dbl,s,re1] &&
	getBalance[u,re1.ure.udb,u2] &&
	withdrawWithLog[u,t,n2,rid,l,dbr,re1.ure.udb,re1.lre.ldb,s,re2] &&
	getBalance[u,re2.wre.ure.udb,u3] => {
		s.value = false => u3.balance = u1.balance
		s.value = true && u1 != null => u2.balance = add[u1.balance, n1]
		s.value = true && u1 != null && no dbr.datas && n1 = n2 => u3.balance = u1.balance
		s.value = true && u1 != null && no dbr.datas && n2 > add[u1.balance, n1] => u3.balance = u2.balance
		s.value = true => re1.lre.log.op = RC
		s.value = true => re2.lre.log.op = WD
	}
}for 20

//2.查询-提现-查询-提现-查询（7:频率过高失败，数值变化，日志变化）
check assert7_13 {
	all u,t1,t2,n1,n2:Int, rid:RID, l:Limit, dbr:RDB, dbu:UserDB, dbl:LogDB, s:Status,
		u1,u2,u3:AbsData, re1,re2:WDLReturn |
	getBalance[u,dbu,u1] &&
	withdrawWithLog[u,t1,n1,rid,l,dbr,dbu,dbl,s,re1] &&
	getBalance[u,re1.wre.ure.udb,u2] &&
	withdrawWithLog[u,t2,n2,rid,l,re1.wre.rre.rdb,re1.wre.ure.udb,re1.lre.ldb,s,re2] &&
	getBalance[u,re2.wre.ure.udb,u3] => {
		s.value = false => u3.balance = u1.balance
		s.value = true && no dbr.datas && u1.balance >= n1 => u2.balance = sub[u1.balance, n1]
		s.value = true && no dbr.datas && sub[t2,t1] < l.dur => u3.balance = u2.balance
		s.value = true && no dbr.datas && sub[t2,t1] >= l.dur && u1.balance >= add[n1,n2] => u3.balance = sub[u2.balance,n2]
		s.value = true && no dbr.datas && sub[t2,t1] >= l.dur && u2.balance < n2 => u3.balance = u2.balance
		s.value = true => re1.lre.log.op = WD
		s.value = true => re2.lre.log.op = WD
	}
}for 20

//项目和捐赠
//3.创建-捐赠-中止（9:项目金额变化，是否成功中止，用户金额变化，日志变化）
check assert14_22 {
	all uid1,uid2,uid3,uid4,tar,n:Int, c:string, s:Status, ev:Event,
        dbe:EventDB, dbd:DonateDB, dbu:UserDB, dbl:LogDB, 
		u1,u2,u3:AbsData, re1:EventReturn, re2:DLReturn, re3:SPLReturn |
		getBalance[uid1,dbu,u1] &&
		getBalance[uid2,dbu,u2] &&
		createEvent[uid1,tar,c,dbe,re1] &&
		donateWithLog[uid2,re1.id,n,dbd,re1.edb,dbu,dbl,s,re2] &&
		stopAndPayWithLog[uid4,re1.id,re2.dere.ere.edb,re2.dere.ure.udb,re2.lre.ldb,s,re3] &&
		getEvent[re1.id,re3.eure.ere.edb,ev] && 
		getBalance[uid3,re3.eure.ure.udb,u3] => {
			s.value = true && u2.balance >= n => ev.total = n		//25387ms
			s.value = true && u2.balance < n => ev.total = 0		//31901ms	
			s.value = true && uid4 != uid1 => ev.status = true	//31453ms
			s.value = true && uid4 = uid1 => ev.status = false	//85948ms
			s.value = true && u2.balance >= n && uid3 = uid2 && uid1 != uid2 => u3.balance = sub[u2.balance, n]	//35534ms
			s.value = true && u2.balance < n && uid3 = uid2 => u3.balance = u2.balance	//17241ms
			s.value = true && u2.balance < n && uid3 = uid1 => u3.balance = u1.balance	//15162ms
			ev.status = false && uid1 != uid2 && uid3 = uid1 => u3.balance = add[u1.balance, n]	//74979ms
			s.value = true => re3.lre.log.op = SE	//14ms
		}
} for 20
		
//EStop
//4.停止-其他操作(4:中止失败/成功)
check assert23_26 {
	all u,n:Int, dbu:UserDB, dbl:LogDB, s1,s2:Status,
		re1:User, re2:RCReturn |
	getBalance[u,dbu,re1] &&
	estop[s1,u,s2] &&
	rechargeWithLog[u,n,dbu,dbl,s2,re2] => {
		u != s1.admin && s1.value = true => re2.ure.user.balance = add[re1.balance, n]
		u = s1.admin => s2.value = false
		u = s1.admin => re2.ure.udb = dbu
		u = s1.admin => re2.ure.user = null
	}
}for 20
