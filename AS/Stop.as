//6 axioms
package Stop;
{

Spec Status;
	uses Integer, Bool;
	Attr  
		admin: Integer;  
		value: Bool;
End

Spec Estop;
	uses Status,Integer,Bool;
	Retr
		testFunc(Status):Bool;
	Tran  
		estop(Status,Integer):Status;
	Axiom
		For all e:Estop, s:Status, u:Integer that
			e.estop(s, uid).value = false, if u = s.admin;			
			e.estop(s, uid).value = s.value, if u <> s.admin;			
		End

		For all e:Estop, s:Status that
			e.testFunc(s) = true, if s.value = true;			
			e.testFunc(s) = false, if s.value = false;			
		End

		For all e:Estop, u:Int, s:Status that
			e.estop(s1,u);testFunc(s2) = false, if u = s1.admin, s2 = e.estop(s1,u);
			e.estop(s1,u);testFunc(s2) = true, if u = s1.admin, s2 = e.estop(s1,u), s1.value = true;
		End
End
}