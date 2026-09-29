import Mathlib
import Submission.Work.Cert.WL.Defs
import Submission.Work.Cert.LeafAux

namespace Work.Cert.WL

/-!
# The `dvu` lower bound for the ratio error (winding leaf, piece 3)

`(S : ℝ) · (eA·bU + aU·eB)/(Blo·bL) ≤ dvu (mu eA bU + mu aU eB) (md bL Blo)`.

This is the integer-rounded form of the elementary estimate

  `S · N/(Blo·bL) ≤ ⌈M·S/mb⌉`,  `N = eA·bU + aU·eB`,  `M = ⌈eA·bU/S⌉ + ⌈aU·eB/S⌉`,

which follows from the three one-ulp facts for the floored/ceiled integer operations:

* `md bL Blo = ⌊bL·Blo/S⌋ ≤ bL·Blo/S`, so with `N ≥ 0`, `N·mb ≤ N·(bL·Blo)/S`;
* `mu eA bU + mu aU eB ≥ (eA·bU + aU·eB)/S = N/S`, so `N·(bL·Blo)/S ≤ M·(bL·Blo)`;
* `dvu M mb = ⌈M·S/mb⌉ ≥ M·S/mb`.

The hypothesis `0 < md bL Blo` supplies both `mb > 0` and, through
`1 ≤ mb ≤ bL·Blo/S`, the positivity of the denominator `bL·Blo`.
-/
theorem dvu_ratio (eA bU aU eB bL Blo : ℤ) (heA : 0 ≤ eA) (hbU : 0 ≤ bU) (haU : 0 ≤ aU)
    (heB : 0 ≤ eB) (hbL : 0 ≤ bL) (hBlo : 0 ≤ Blo) (hY : 0 < md bL Blo) :
    (S : ℝ) * ((((eA : ℤ) : ℝ) * ((bU : ℤ) : ℝ) + ((aU : ℤ) : ℝ) * ((eB : ℤ) : ℝ)) /
        (((Blo : ℤ) : ℝ) * ((bL : ℤ) : ℝ))) ≤
      ((dvu (mu eA bU + mu aU eB) (md bL Blo) : ℤ) : ℝ) := by
  have hSR : (0:ℝ) < (S:ℝ) := S_posR
  have hmbR : (0:ℝ) < ((md bL Blo : ℤ):ℝ) := by exact_mod_cast hY
  have hmb1 : (1:ℝ) ≤ ((md bL Blo : ℤ):ℝ) := by
    have h : (1:ℤ) ≤ md bL Blo := hY
    exact_mod_cast h
  -- `md bL Blo = ⌊bL·Blo/S⌋`
  have hmd := md_le bL Blo
  -- the denominator is positive: `1 ≤ mb ≤ bL·Blo/S`
  have hLpos : (0:ℝ) < (bL:ℝ)*(Blo:ℝ) := by
    have h3 : (1:ℝ) ≤ (bL:ℝ)*(Blo:ℝ)/(S:ℝ) := le_trans hmb1 hmd
    rw [le_div_iff₀ hSR] at h3
    nlinarith [h3, hSR]
  have hXpos : (0:ℝ) < (Blo:ℝ)*(bL:ℝ) := by simpa [mul_comm] using hLpos
  have heAr : (0:ℝ) ≤ (eA:ℝ) := by exact_mod_cast heA
  have hbUr : (0:ℝ) ≤ (bU:ℝ) := by exact_mod_cast hbU
  have haUr : (0:ℝ) ≤ (aU:ℝ) := by exact_mod_cast haU
  have heBr : (0:ℝ) ≤ (eB:ℝ) := by exact_mod_cast heB
  have hbLr : (0:ℝ) ≤ (bL:ℝ) := by exact_mod_cast hbL
  have hBlor : (0:ℝ) ≤ (Blo:ℝ) := by exact_mod_cast hBlo
  have hNnn : (0:ℝ) ≤ (eA:ℝ)*(bU:ℝ) + (aU:ℝ)*(eB:ℝ) :=
    add_nonneg (mul_nonneg heAr hbUr) (mul_nonneg haUr heBr)
  -- `(eA·bU + aU·eB)/S ≤ mu eA bU + mu aU eB`
  have hMu : ((eA:ℝ)*(bU:ℝ) + (aU:ℝ)*(eB:ℝ))/(S:ℝ) ≤
      ((mu eA bU + mu aU eB : ℤ):ℝ) := by
    have h1 := mu_ge eA bU
    have h2 := mu_ge aU eB
    rw [add_div]
    push_cast
    linarith
  -- the cross-multiplied core inequality
  have hkey : ((eA:ℝ)*(bU:ℝ) + (aU:ℝ)*(eB:ℝ)) * ((md bL Blo:ℤ):ℝ)
      ≤ ((mu eA bU + mu aU eB : ℤ):ℝ) * ((Blo:ℝ)*(bL:ℝ)) := by
    have hMnn : (0:ℝ) ≤ (bL:ℝ)*(Blo:ℝ) := le_of_lt hLpos
    have h1 : ((eA:ℝ)*(bU:ℝ) + (aU:ℝ)*(eB:ℝ)) * ((md bL Blo:ℤ):ℝ)
        ≤ ((eA:ℝ)*(bU:ℝ) + (aU:ℝ)*(eB:ℝ)) * ((bL:ℝ)*(Blo:ℝ)/(S:ℝ)) :=
      mul_le_mul_of_nonneg_left hmd hNnn
    have h2 : ((eA:ℝ)*(bU:ℝ) + (aU:ℝ)*(eB:ℝ)) * ((bL:ℝ)*(Blo:ℝ)/(S:ℝ))
        ≤ ((mu eA bU + mu aU eB : ℤ):ℝ) * ((Blo:ℝ)*(bL:ℝ)) := by
      have he : ((eA:ℝ)*(bU:ℝ) + (aU:ℝ)*(eB:ℝ)) * ((bL:ℝ)*(Blo:ℝ)/(S:ℝ))
          = (((eA:ℝ)*(bU:ℝ) + (aU:ℝ)*(eB:ℝ))/(S:ℝ)) * ((bL:ℝ)*(Blo:ℝ)) := by ring
      rw [he]
      calc (((eA:ℝ)*(bU:ℝ) + (aU:ℝ)*(eB:ℝ))/(S:ℝ)) * ((bL:ℝ)*(Blo:ℝ))
          ≤ ((mu eA bU + mu aU eB : ℤ):ℝ) * ((bL:ℝ)*(Blo:ℝ)) :=
            mul_le_mul_of_nonneg_right hMu hMnn
        _ = ((mu eA bU + mu aU eB : ℤ):ℝ) * ((Blo:ℝ)*(bL:ℝ)) := by ring
    linarith
  have hA : ((eA:ℝ)*(bU:ℝ) + (aU:ℝ)*(eB:ℝ)) / ((Blo:ℝ)*(bL:ℝ))
      ≤ ((mu eA bU + mu aU eB : ℤ):ℝ) / ((md bL Blo:ℤ):ℝ) := by
    rw [div_le_div_iff₀ hXpos hmbR]
    exact hkey
  have hmain : (S:ℝ) * (((eA:ℝ)*(bU:ℝ) + (aU:ℝ)*(eB:ℝ)) / ((Blo:ℝ)*(bL:ℝ)))
      ≤ ((dvu (mu eA bU + mu aU eB) (md bL Blo) : ℤ):ℝ) := by
    calc (S:ℝ) * (((eA:ℝ)*(bU:ℝ) + (aU:ℝ)*(eB:ℝ)) / ((Blo:ℝ)*(bL:ℝ)))
        ≤ (S:ℝ) * (((mu eA bU + mu aU eB : ℤ):ℝ) / ((md bL Blo:ℤ):ℝ)) :=
          mul_le_mul_of_nonneg_left hA (le_of_lt hSR)
      _ = ((mu eA bU + mu aU eB : ℤ):ℝ) * (S:ℝ) / ((md bL Blo:ℤ):ℝ) := by ring
      _ ≤ ((dvu (mu eA bU + mu aU eB) (md bL Blo) : ℤ):ℝ) := dvu_ge hY
  exact hmain

end Work.Cert.WL
