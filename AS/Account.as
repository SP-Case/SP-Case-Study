//20 axioms
package Account;
import UtilOp;
{
Spec User;
extends AbsData;
	uses Integer;
	Attr
		balance:Integer;
	Axiom
		For all u:User that
			u.balance > 0;
		End
End

Spec UserDB;
	uses User;
	Attr
		datas[0..*]:User;
End

Spec UserReturn;
	uses User,AbsData,Integer;
	Attr
		id:Integer;
		user:AbsData;
		udb:UserDB;
End

Spec Account;
	uses UtilOp,AbsData,UserReturn,UserDB,Integer;
	Retr
		getBalance(Integer,UserDB):AbsData;
	Tran
		addBalance(Integer,Integer,UserDB):UserReturn;
		subBalance(Integer,Integer,UserDB):UserReturn;
	Axiom
		For all a:Account, util:UtilOp, uid:Integer, db:UserDB that
			a.getBalance(uid,db) = null, if util.getDataById(uid,db) = nil;
			a.getBalance(uid,db) = util.getDataById(uid,db), if util.getDataById(uid,db) <> nil;
		End

		For all a:Account, util:UtilOp, uid,n:Integer, db:UserDB that
			n > 0;
			let 
				u = util.getDataById(uid,db) 
				re = a.addBalance(uid,db)
			in
				re.user.balance = u.balance + n, if u <> nil;
				re.udb.datas = util.union(util.sub(db.datas, u), re.user), if u <> nil;
				re.user = null, if u = nil;
				re.udb = db, if u = nil;
			End
		End

		For all a:Account, util:UtilOp, uid,n:Integer, db:UserDB that
			n > 0;
			let 
				u = util.getDataById(uid,db) 
				re = a.subBalance(uid,db)
			in
				re.user.balance = u.balance - n, if u <> nil, u.balance - n >= 0;
				re.udb.datas = util.union(util.sub(db.datas, u), re.user), if u <> nil, u.balance - n >= 0;
				re.user = null, if u = nil;
				re.udb = db, if u = nil;
				re.user = null, if u.balance - n < 0;
				re.udb = db, if u.balance - n < 0;
			End
		End

		For all a:Account, util:UtilOp, uid,n:Integer, db:UserDB that
			let u = a.getBalance(uid,db) in
				a.getBalance(uid, a.addBalance(uid,n,db).udb).balance = u.balance + n, if u <> null;
			End
		End

		For all a:Account, util:UtilOp, uid,n:Integer, db:UserDB that
			let u = a.getBalance(uid,db) in
				a.getBalance(uid, a.subBalance(uid,n,db).udb).balance = u.balance, if u <> null, n > u.balance;
				a.getBalance(uid, a.subBalance(uid,n,db).udb).balance = u.balance - n, if u <> null, n <= u.balance;
			End
		End

		For all a:Account, util:UtilOp, uid,n1,n2:Integer, db:UserDB that
			let u = a.getBalance(uid,db) in
				a.subBalance(uid, n2, a.addBalance(uid,n1,db).udb).user.balance = u.balance, if u <> null, n1 = n2;
				a.subBalance(uid, n2, a.addBalance(uid,n1,db).udb).user = null, if u <> null, n2 > u.balance + n1;
			End
		End
End
}