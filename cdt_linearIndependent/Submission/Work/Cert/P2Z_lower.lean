import Mathlib
import Submission.Work.Cert.LeafAux

namespace Work.Cert

/-- One squaring step of the `mu` chain: from `0 ≤ c ≤ r` (with `c` real, `r` integer) we get
`c²/S ≤ mu r r = ⌈r²/S⌉`. -/
lemma mu_sq_lower {c : ℝ} {r : ℤ} (hc : 0 ≤ c) (hr : c ≤ (r : ℝ)) :
    c ^ 2 / (S : ℝ) ≤ ((mu r r : ℤ) : ℝ) := by
  have hS : (0:ℝ) < (S:ℝ) := by exact_mod_cast S_pos
  have h1 : (r : ℝ) * (r : ℝ) / (S : ℝ) ≤ ((mu r r : ℤ) : ℝ) := mu_ge r r
  have h2 : c * c ≤ (r : ℝ) * (r : ℝ) := mul_self_le_mul_self hc hr
  have h3 : c ^ 2 / (S : ℝ) ≤ (r : ℝ) * (r : ℝ) / (S : ℝ) := by
    apply div_le_div_of_nonneg_right _ hS.le
    simpa [sq] using h2
  linarith

/-- Lower bound for `ratioZ Aup Blo = ⌈(⌈Aup²/S⌉)·S/⌊Blo²/S⌋⌉`. -/
lemma ratioZ_lower (Aup Blo : ℤ) (hBlo : 0 < Blo) (hmd : 0 < md Blo Blo) :
    (Aup : ℝ) ^ 2 * (S : ℝ) / (Blo : ℝ) ^ 2 ≤ ((ratioZ Aup Blo : ℤ) : ℝ) := by
  have hS : (0:ℝ) < (S:ℝ) := by exact_mod_cast S_pos
  have hSR : (S:ℝ) ≠ 0 := ne_of_gt hS
  have hbR : (0:ℝ) < (Blo:ℝ) := by exact_mod_cast hBlo
  have hmdR : (0:ℝ) < ((md Blo Blo : ℤ):ℝ) := by exact_mod_cast hmd
  have h1 : ((mu Aup Aup : ℤ):ℝ) * (S:ℝ) / ((md Blo Blo : ℤ):ℝ)
      ≤ ((ratioZ Aup Blo : ℤ):ℝ) := by
    unfold ratioZ
    exact dvu_ge hmd
  have hms : (Aup:ℝ)^2 ≤ ((mu Aup Aup : ℤ):ℝ) * (S:ℝ) := by
    have hm := mu_ge Aup Aup
    have e : (Aup:ℝ)*(Aup:ℝ)/(S:ℝ) = (Aup:ℝ)^2/(S:ℝ) := by ring
    rw [e] at hm
    have h := mul_le_mul_of_nonneg_right hm hS.le
    rwa [div_mul_cancel₀ _ hSR] at h
  have h2 : (Aup:ℝ)^2 / ((md Blo Blo:ℤ):ℝ)
      ≤ ((mu Aup Aup:ℤ):ℝ)*(S:ℝ)/((md Blo Blo:ℤ):ℝ) :=
    div_le_div_of_nonneg_right hms hmdR.le
  have hdle : ((md Blo Blo:ℤ):ℝ) ≤ (Blo:ℝ)^2/(S:ℝ) := by
    have h := md_le Blo Blo
    have e : (Blo:ℝ)*(Blo:ℝ)/(S:ℝ) = (Blo:ℝ)^2/(S:ℝ) := by ring
    rwa [e] at h
  have h3 : (Aup:ℝ)^2 * (S:ℝ) / (Blo:ℝ)^2 ≤ (Aup:ℝ)^2 / ((md Blo Blo:ℤ):ℝ) := by
    rw [show (Aup:ℝ)^2 * (S:ℝ) / (Blo:ℝ)^2 = (Aup:ℝ)^2 / ((Blo:ℝ)^2/(S:ℝ)) by
      field_simp]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hmdR hdle
  linarith

/-- The four-squaring chain giving `Aup^16·S/Blo^16 ≤ r8Z Aup Blo`. -/
lemma r8Z_lower (Aup Blo : ℤ) (hBlo : 0 < Blo) (hmd : 0 < md Blo Blo) :
    (Aup:ℝ)^16 * (S:ℝ) / (Blo:ℝ)^16 ≤ ((r8Z Aup Blo : ℤ):ℝ) := by
  have hS : (0:ℝ) < (S:ℝ) := by exact_mod_cast S_pos
  have hbR : (0:ℝ) < (Blo:ℝ) := by exact_mod_cast hBlo
  have h0 := ratioZ_lower Aup Blo hBlo hmd
  have hc0 : (0:ℝ) ≤ (Aup:ℝ)^2 * (S:ℝ) / (Blo:ℝ)^2 := by positivity
  have h1 := mu_sq_lower hc0 h0
  have e1 : ((Aup:ℝ)^2 * (S:ℝ) / (Blo:ℝ)^2)^2 / (S:ℝ)
      = (Aup:ℝ)^4 * (S:ℝ) / (Blo:ℝ)^4 := by
    field_simp
  rw [e1] at h1
  have hc1 : (0:ℝ) ≤ (Aup:ℝ)^4 * (S:ℝ) / (Blo:ℝ)^4 := by positivity
  have h2 := mu_sq_lower hc1 h1
  have e2 : ((Aup:ℝ)^4 * (S:ℝ) / (Blo:ℝ)^4)^2 / (S:ℝ)
      = (Aup:ℝ)^8 * (S:ℝ) / (Blo:ℝ)^8 := by
    field_simp
  rw [e2] at h2
  have hc2 : (0:ℝ) ≤ (Aup:ℝ)^8 * (S:ℝ) / (Blo:ℝ)^8 := by positivity
  have h3 := mu_sq_lower hc2 h2
  have e3 : ((Aup:ℝ)^8 * (S:ℝ) / (Blo:ℝ)^8)^2 / (S:ℝ)
      = (Aup:ℝ)^16 * (S:ℝ) / (Blo:ℝ)^16 := by
    field_simp
  rw [e3] at h3
  unfold r8Z
  exact h3

/-- The `m`-side: `65536·(m²/S) ≤ µ(65536·S, ⌈m²/S⌉)`. -/
lemma m_chain (m : ℤ) :
    (65536:ℝ) * ((m:ℝ)^2/(S:ℝ)) ≤ ((mu (65536*S) (mu m m) : ℤ):ℝ) := by
  have hS : (0:ℝ) < (S:ℝ) := by exact_mod_cast S_pos
  have h1 : ((65536*S : ℤ):ℝ) * ((mu m m : ℤ):ℝ) / (S:ℝ)
      ≤ ((mu (65536*S) (mu m m) : ℤ):ℝ) := mu_ge (65536*S) (mu m m)
  have e : ((65536*S : ℤ):ℝ) * ((mu m m : ℤ):ℝ) / (S:ℝ) = 65536 * ((mu m m : ℤ):ℝ) := by
    push_cast
    field_simp
  rw [e] at h1
  have h2 : (65536:ℝ) * ((m:ℝ)^2/(S:ℝ)) ≤ 65536 * ((mu m m : ℤ):ℝ) := by
    have hm := mu_ge m m
    have e2 : (m:ℝ)*(m:ℝ)/(S:ℝ) = (m:ℝ)^2/(S:ℝ) := by ring
    rw [e2] at hm
    exact mul_le_mul_of_nonneg_left hm (by norm_num)
  linarith

/-- Generic assembly: the `r8` bound and the `m` bound combine. -/
lemma generic_lower (s a b mm X R8 P : ℝ) (hs : 0 < s) (hb : 0 < b)
    (hR80 : 0 ≤ R8)
    (hX : 65536 * (mm^2/s) ≤ X) (hr8 : a^16*s/b^16 ≤ R8) (hP : X*R8/s ≤ P) :
    65536 * mm^2 * a^16 / (b^16 * s) ≤ P := by
  have hb16 : b^16 ≠ 0 := pow_ne_zero 16 (ne_of_gt hb)
  have hs0 : s ≠ 0 := ne_of_gt hs
  have e : 65536 * (mm^2/s) * (a^16*s/b^16) / s = 65536 * mm^2 * a^16 / (b^16 * s) := by
    field_simp
  rw [← e]
  have hcoef : (0:ℝ) ≤ 65536 * (mm^2/s) := by positivity
  calc 65536 * (mm^2/s) * (a^16*s/b^16) / s
      ≤ 65536 * (mm^2/s) * R8 / s := by
        apply div_le_div_of_nonneg_right _ hs.le
        exact mul_le_mul_of_nonneg_left hr8 hcoef
    _ ≤ X * R8 / s := by
        apply div_le_div_of_nonneg_right _ hs.le
        exact mul_le_mul_of_nonneg_right hX hR80
    _ ≤ P := hP

theorem P2Z_lower (Aup Blo m : ℤ) (hBlo : 0 < Blo) (hmd : 0 < Work.Cert.md Blo Blo) :
    (65536 * (m : ℝ) ^ 2 * (Aup : ℝ) ^ 16) / ((Blo : ℝ) ^ 16 * (Work.Cert.S : ℝ))
      ≤ ((Work.Cert.P2Z Aup Blo m : ℤ) : ℝ) := by
  have hS : (0:ℝ) < (S:ℝ) := by exact_mod_cast S_pos
  have hbR : (0:ℝ) < (Blo:ℝ) := by exact_mod_cast hBlo
  have hr8 := r8Z_lower Aup Blo hBlo hmd
  have hX := m_chain m
  have hP : ((mu (65536*S) (mu m m) : ℤ):ℝ) * ((r8Z Aup Blo : ℤ):ℝ) / (S:ℝ)
      ≤ ((mu (mu (65536*S) (mu m m)) (r8Z Aup Blo) : ℤ):ℝ) := mu_ge _ _
  have hR80 : (0:ℝ) ≤ ((r8Z Aup Blo : ℤ):ℝ) := le_trans (by positivity) hr8
  have key := generic_lower (S:ℝ) (Aup:ℝ) (Blo:ℝ) (m:ℝ)
      ((mu (65536*S) (mu m m) : ℤ):ℝ) ((r8Z Aup Blo : ℤ):ℝ)
      ((mu (mu (65536*S) (mu m m)) (r8Z Aup Blo) : ℤ):ℝ)
      hS hbR hR80 hX hr8 hP
  unfold P2Z
  exact key

end Work.Cert
