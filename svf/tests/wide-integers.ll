; Keep the wide operations as instructions so AE runs its transfer functions.
target datalayout = "e-p:64:64"
@wide = global i256 1606938044258990275541962092341162602522202993782792835301383

declare void @svf_assert(i32)

define i32 @main() {
entry:
  %a = add i128 9223372036854775808, 5
  %b = zext i64 -1 to i128
  %c = lshr i128 -2, 64
  %d = trunc i128 %b to i9
  %e = sext i9 %d to i128
  %f = add i128 170141183460469231731687303715884105727, 1
  %g = udiv i128 -2, 2
  %h = load i256, ptr @wide
  %i = shl i256 1, 200
  %j = add i256 %i, 7
  %k = getelementptr i256, ptr @wide, i128 18446744073709551616
  %l = load i256, ptr %k
  %a.ok = icmp eq i128 %a, 9223372036854775813
  %b.ok = icmp eq i128 %b, 18446744073709551615
  %c.ok = icmp eq i128 %c, %b
  %e.ok = icmp eq i128 %e, -1
  %f.ok = icmp slt i128 %f, 0
  %g.ok = icmp eq i128 %g, 170141183460469231731687303715884105727
  %h.ok = icmp eq i256 %h, %j
  %k.ok = icmp eq i256 %l, %j
  %u.ok = icmp ugt i128 -1, 9223372036854775808
  %s.ok = icmp slt i128 -1, 9223372036854775808
  %ab = and i1 %a.ok, %b.ok
  %ce = and i1 %c.ok, %e.ok
  %fg = and i1 %f.ok, %g.ok
  %hk = and i1 %h.ok, %k.ok
  %us = and i1 %u.ok, %s.ok
  %abce = and i1 %ab, %ce
  %fghk = and i1 %fg, %hk
  %all = and i1 %abce, %fghk
  %ok = and i1 %all, %us
  %check = zext i1 %ok to i32
  call void @svf_assert(i32 %check)
  ret i32 0
}
