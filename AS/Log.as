//10 axioms
package Log;
import UtilOp;
{

Spec Log;
extends AbsData;
	uses Integer, OpType;
	Attr
		uid: Integer;
		op: OpType;
End

Spec LogDB;
	uses Log;
	Attr
		datas[0..*]:Log;
End

Spec LogReturn;
	uses Integer, Log, LogDB;
	Attr
		id:Integer;
		log:Log;
		ldb:LogDB;
End

Spec ReturnWithLog;
	uses LogReturn;
	Attr
		lre:LogReturn;
End

Spec LogM;
	uses Integer, Log, LogDB, OpType;
	Tran
		log(Integer, OpType, LogDB): LogReturn;
		testFunc(Integer, LogDB): LogReturn;
	Axiom
		For all l:LogM, uop:UtilOp, u:Int, o:OpType, db:LogDB that
			uop.isin(l.log(u,o,db).log, db.datas) = false;
			l.log(u,o,db).log.uid = u;	
			l.log(u,o,db).log.op = o;
			l.log(u,o,db).ldb.datas = uop.union(db.datas, l.log(u,o,db).log);
		End

		For all l:LogM, u:Int, db:LogDB that
			l.testFunc(u,db) = l.log(u,TEST,db);
		End

		For all l:LogM, uop:UtilOp, u1,u2:Int, db1,db2:LogDB that
			let 
			    re1 = l.testFunc(u1,db1) 
			    re2 = l.testFunc(u2,db2) 
			in
				re1.log.uid = u1;
				re1.log.op = TEST;
				re2.log.uid = u2;
				re2.log.op = TEST;
				re2.ldb.datas = uop.union(uop.union(db1.datas,re1.log),re2.log);
			End
		End
End
}