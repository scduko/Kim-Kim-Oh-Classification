import KimKimOh.Assembly
import KimKimOh.Bridge.LocalGlobal
import KimKimOh.HostData
import KimKimOh.FirstPassChecks.All3
import KimKimOh.FirstPassChecks.All9
import KimKimOh.Terminal.All3
import KimKimOh.Terminal.All9
import KimKimOh.Terminal.TabCheck

/-!
# Theorem 1.2

`mainTheorem`: Theorem 1.2, without hypotheses. §4 is `minTwo6`, `minTwo9`:
`minTwo_of_checks` for the two host decompositions, with the local–global principle for `K₃` and
`K₉` (`localGlobal_K3`, `localGlobal_K9`, `Bridge/LocalGlobal.lean`) and the kernel checks of the
first pass (`FirstPassChecks`), of the last-column test, the enumeration and the witnesses
(`Terminal`), and of their tables.
-/

namespace KimKimOh

open Tables

theorem mxTab_all : ∀ blk < 729, mxRowOK (tget mxTab 729 blk) (tget mwTab 3645 blk) blk = true :=
  mx_all fun i hi => by
    interval_cases i
    exacts [mxTab_ok0, mxTab_ok1, mxTab_ok2, mxTab_ok3, mxTab_ok4, mxTab_ok5, mxTab_ok6, mxTab_ok7,
      mxTab_ok8]

/-- **§4 for `L₆`** (Theorem 1.2(i)): every maximal reduced ternary of minimum at least 2. -/
theorem minTwo6 : MinTwo6 :=
  minTwo_of_checks host3 region3 localGlobal_K3 L6 L6_represents_K3_line tableOK2_3 tableOK3_3
    heavy3 leftsData3 dispatch3 enum3_all r2Tab_ok mxTab_all termAll3

/-- **§4 for `L₉`** (Theorem 1.2(ii)): every maximal reduced ternary of minimum at least 2. -/
theorem minTwo9 : MinTwo9 :=
  minTwo_of_checks host9 region9 localGlobal_K9 L9 L9_represents_K9_line tableOK2_9 tableOK3_9
    heavy9 leftsData9 dispatch9 enum9_all r2Tab_ok mxTab_all termAll9

/-- **Theorem 1.2** (`thm:main`). -/
theorem mainTheorem : MainTheorem :=
  mainTheorem_of_minTwo minTwo6 minTwo9

end KimKimOh
