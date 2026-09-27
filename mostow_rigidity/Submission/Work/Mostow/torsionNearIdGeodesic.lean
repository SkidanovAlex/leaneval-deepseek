import Mathlib
import Submission.Work.Mostow.ellipticAux
import Submission.Work.Mostow.elliptic_normal_form
import Submission.Work.Mostow.blk_hom
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.conj_fundamentalDomain
import Submission.Work.Mostow.boundedTorsionAux
import Submission.Work.Mostow.even_normal_dim
import Submission.Work.Mostow.fermiLineTwo
import Submission.Work.Mostow.ftbPivotAux
import Submission.Work.Mostow.nearIdAt_conj
import Submission.Work.Mostow.poAction_hypIso_zero
import Submission.Work.Mostow.margulisPairDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ## Transport along an equality of ambient dimensions -/

private theorem tnidg_volH_cast {a b : ℕ} (e : a = b) (s : Set (E a)) :
    volH b (e ▸ s) = volH a s := by cases e; rfl

private theorem tnidg_isDiscrete_cast {a b : ℕ} (e : a = b) (Λ : Subgroup (PO b 1)) :
    _root_.IsDiscrete (SetLike.coe Λ) →
      _root_.IsDiscrete (SetLike.coe (e.symm ▸ Λ : Subgroup (PO a 1))) := by
  cases e; exact id

private theorem tnidg_isFundamentalDomain_cast {a b : ℕ} (e : a = b) (Λ : Subgroup (PO b 1))
    (D : Set (E b)) :
    IsFundamentalDomain Λ D (volH b) →
      IsFundamentalDomain (e.symm ▸ Λ : Subgroup (PO a 1)) (e.symm ▸ D) (volH a) := by
  cases e; exact id

private theorem tnidg_mem_cast {a b : ℕ} (e : a = b) (Λ : Subgroup (PO b 1)) (x : PO a 1) :
    (e ▸ x : PO b 1) ∈ Λ → x ∈ (e.symm ▸ Λ : Subgroup (PO a 1)) := by
  cases e; exact id

private theorem tnidg_cast_self_po {a : ℕ} (e : a = a) (X : PO a 1) :
    (e ▸ X : PO a 1) = X := by cases e; rfl

private theorem tnidg_cast_eq_one {a b : ℕ} (e : a = b) (X : PO a 1) (h : X = 1) :
    (e ▸ X : PO b 1) = 1 := by cases e; simpa using h

private theorem tnidg_nearIdAt_mono {n : ℕ} {g : PO n 1} {z : E n} {η η' : ℝ}
    (h : NearIdAt g z η) (hle : η ≤ η') : NearIdAt g z η' :=
  fun u hu => lt_of_lt_of_le (h u hu) hle

/-! ## The small-volume threshold -/

private theorem tnidg_eta0 (V c α : ℝ) (hc : 0 < c) (hα : 0 < α) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ENNReal.ofReal V < ENNReal.ofReal (c * η ^ (-α)) := by
  set s : ℝ := max V 0 + 1 with hs
  have hs_pos : 0 < s := by rw [hs]; linarith [le_max_right V 0]
  have hVs : V < s := by rw [hs]; linarith [le_max_left V 0]
  have hcs : 0 < c / s := div_pos hc hs_pos
  refine ⟨(c / s) ^ (1 / α), Real.rpow_pos_of_pos hcs _, ?_⟩
  intro η hη hηle
  have hmono : ((c / s) ^ (1 / α)) ^ (-α) ≤ η ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos hη hηle (by linarith)
  have hval : ((c / s) ^ (1 / α)) ^ (-α) = s / c := by
    rw [← Real.rpow_mul (le_of_lt hcs)]
    have h1 : (1 / α) * (-α) = -1 := by field_simp
    rw [h1, Real.rpow_neg_one]
    field_simp
  have h2 : s / c ≤ η ^ (-α) := by rw [← hval]; exact hmono
  have h4 : c * (s / c) = s := by field_simp
  have hge : s ≤ c * η ^ (-α) := by
    have h3 : c * (s / c) ≤ c * η ^ (-α) := mul_le_mul_of_nonneg_left h2 (le_of_lt hc)
    linarith
  exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos hc (Real.rpow_pos_of_pos hη _))).mpr
    (lt_of_lt_of_le hVs hge)

/-! ## The volume gap applied to a near-identity block element -/

private theorem tnidg_gapBlock (m : ℕ)
    (hAall : ∀ k, POActionProp k) (hIall : ∀ k, HypIsometryProp k)
    (θ₀ c α : ℝ)
    (hgap : ∀ (j m' : ℕ) (hjm : j + m' = 1 + m) (Λ : Subgroup (PO (j + m') 1)) (D : Set (E (j + m'))) (R : E m' ≃ₗᵢ[ℝ] E m') (u : E (j + m')) (θ : ℝ), 2 ≤ j → 1 ≤ m' → _root_.IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (j + m')) → blk j m' 1 R ∈ Λ → (∀ w : E m', R w = w → w = 0) → NearIdAt (blk j m' 1 R) u θ → 0 < θ → θ ≤ θ₀ → ENNReal.ofReal (c * θ ^ (-α)) ≤ volH (j + m') D)
    (j m' : ℕ) (hjm : j + m' = 1 + m) (hj : 2 ≤ j) (hm' : 1 ≤ m')
    (Λ : Subgroup (PO (1 + m) 1)) (hdisc : _root_.IsDiscrete (SetLike.coe Λ))
    (D : Set (E (1 + m))) (hD : IsFundamentalDomain Λ D (volH (1 + m)))
    (R : E m' ≃ₗᵢ[ℝ] E m') (hRfree : ∀ w : E m', R w = w → w = 0)
    (h : PO (1 + m) 1) (w : E (1 + m)) (θ : ℝ) (hθ : 0 < θ) (hθθ : θ ≤ θ₀)
    (hmem : (hjm ▸ blk j m' 1 R : PO (1 + m) 1) ∈ Λ.map (MulAut.conj h⁻¹).toMonoidHom)
    (hnear : NearIdAt (hjm ▸ blk j m' 1 R : PO (1 + m) 1) w θ) :
    ENNReal.ofReal (c * θ ^ (-α)) ≤ volH (1 + m) D := by
  have hA1 : POActionProp (1 + m) := hAall (1 + m)
  have hI1 : HypIsometryProp (1 + m) := hIall (1 + m)
  set Λ₁ : Subgroup (PO (1 + m) 1) := Λ.map (MulAut.conj h⁻¹).toMonoidHom with hΛ₁
  set D₁ : Set (E (1 + m)) := (fun u : E (1 + m) => h⁻¹ • u) '' D with hD₁
  have hdisc₁ : _root_.IsDiscrete (SetLike.coe Λ₁) := isDiscrete_map_conj hdisc h
  have hD₁ : IsFundamentalDomain Λ₁ D₁ (volH (1 + m)) :=
    conj_fundamentalDomain (1 + m) hA1 hI1 Λ D hD h⁻¹
  have hvol₁ : volH (1 + m) D₁ = volH (1 + m) D := volH_smul_image hA1 hI1 h⁻¹ D
  have hdisc' : _root_.IsDiscrete (SetLike.coe (hjm.symm ▸ Λ₁ : Subgroup (PO (j + m') 1))) :=
    tnidg_isDiscrete_cast hjm Λ₁ hdisc₁
  have hD' : IsFundamentalDomain (hjm.symm ▸ Λ₁ : Subgroup (PO (j + m') 1))
      (hjm.symm ▸ D₁) (volH (j + m')) := tnidg_isFundamentalDomain_cast hjm Λ₁ D₁ hD₁
  have hmem' : blk j m' 1 R ∈ (hjm.symm ▸ Λ₁ : Subgroup (PO (j + m') 1)) :=
    tnidg_mem_cast hjm Λ₁ (blk j m' 1 R) hmem
  have hnear' : NearIdAt (blk j m' 1 R) (hjm.symm ▸ w) θ :=
    nearIdAt_cast hjm (blk j m' 1 R) w θ hnear
  have hconcl := hgap j m' hjm (hjm.symm ▸ Λ₁) (hjm.symm ▸ D₁) R (hjm.symm ▸ w) θ
    hj hm' hdisc' hD' hmem' hRfree hnear' hθ hθθ
  have hvol' : volH (j + m') (hjm.symm ▸ D₁) = volH (1 + m) D₁ :=
    tnidg_volH_cast hjm.symm D₁
  rw [hvol', hvol₁] at hconcl
  exact hconcl

/-! ## The conclusion from a block of stratum dimension one -/

/-- If `g` is conjugate (by `h`) to a block `e ▸ blk 1 a 1 R` of stratum dimension one whose
normal part `R` has no nonzero fixed vector, then `g` is conjugate to a block `blk 1 b 1 R'` at the
ambient dimension `1 + b`, with `R'` again fixed-vector-free.  (The two ambient dimensions
`1 + a` and `1 + b` are the same.) -/
private theorem tnidg_concl_of_block {a b : ℕ} (e : 1 + a = 1 + b) (R : E a ≃ₗᵢ[ℝ] E a)
    (hR : ∀ w : E a, R w = w → w = 0) (h g : PO (1 + b) 1)
    (hh : h⁻¹ * g * h = (e ▸ blk 1 a 1 R : PO (1 + b) 1)) :
    ∃ (h' : PO (1 + b) 1) (R' : E b ≃ₗᵢ[ℝ] E b), (∀ W : E b, R' W = W → W = 0) ∧
      g * h' = h' * blk 1 b 1 R' := by
  have e' : a = b := Nat.add_left_cancel e
  have hh' : h⁻¹ * g * h = (congrArg (fun n => 1 + n) e' ▸ blk 1 a 1 R : PO (1 + b) 1) := by
    rw [← congrArg (fun (q : 1 + a = 1 + b) => (q ▸ blk 1 a 1 R : PO (1 + b) 1))
      (Subsingleton.elim e (congrArg (fun n => 1 + n) e'))]
    exact hh
  cases e'
  have hh'' : h⁻¹ * g * h = blk 1 a 1 R := hh'
  refine ⟨h, R, hR, ?_⟩
  have hg_eq : g = h * blk 1 a 1 R * h⁻¹ := by
    calc g = h * (h⁻¹ * g * h) * h⁻¹ := by group
      _ = h * blk 1 a 1 R * h⁻¹ := by rw [hh'']
  rw [hg_eq]
  group

theorem torsionNearIdGeodesic (m : ℕ) (hm : 4 ≤ m) (hev : Even m) (hA : ∀ k, 1 ≤ k → Submission.Mostow.POActionProp k) (hI : ∀ k, 1 ≤ k → Submission.Mostow.HypIsometryProp k) (θ₀ c α : ℝ) (hθ₀ : 0 < θ₀) (hc : 0 < c) (hα : 0 < α) (hgap : ∀ (j m' : ℕ) (hjm : j + m' = 1 + m) (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (j + m') 1)) (D : Set (Submission.Mostow.E (j + m'))) (R : Submission.Mostow.E m' ≃ₗᵢ[ℝ] Submission.Mostow.E m') (u : Submission.Mostow.E (j + m')) (θ : ℝ), 2 ≤ j → 1 ≤ m' → _root_.IsDiscrete (SetLike.coe Λ) → MeasureTheory.IsFundamentalDomain Λ D (Submission.Mostow.volH (j + m')) → Submission.Mostow.blk j m' 1 R ∈ Λ → (∀ w : Submission.Mostow.E m', R w = w → w = 0) → Submission.Mostow.NearIdAt (Submission.Mostow.blk j m' 1 R) u θ → 0 < θ → θ ≤ θ₀ → ENNReal.ofReal (c * θ ^ (-α)) ≤ Submission.Mostow.volH (j + m') D) : ∀ V : ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) (D : Set (Submission.Mostow.E (1 + m))) (z : Submission.Mostow.E (1 + m)) (g : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1), _root_.IsDiscrete (SetLike.coe Λ) → MeasureTheory.IsFundamentalDomain Λ D (Submission.Mostow.volH (1 + m)) → Submission.Mostow.volH (1 + m) D ≤ ENNReal.ofReal V → g ∈ Λ → g ≠ 1 → IsOfFinOrder g → Submission.Mostow.NearIdAt g z η → ∃ (h : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m), (∀ W : Submission.Mostow.E m, R W = W → W = 0) ∧ g * h = h * Submission.Mostow.blk 1 m 1 R 
:= by
  intro V
  have hAall : ∀ k, Submission.Mostow.POActionProp k := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk]; exact poAction_hypIso_zero.1
    · exact hA k hk
  have hIall : ∀ k, Submission.Mostow.HypIsometryProp k := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk]; exact poAction_hypIso_zero.2
    · exact hI k hk
  obtain ⟨ηEN, hηENpos, hEN⟩ := even_normal_dim
  obtain ⟨ηg, hηgpos, hηgbig⟩ := tnidg_eta0 V c α hc hα
  set ρ : ℝ := min (1 / 2) ηEN with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min (by norm_num) hηENpos
  have hρ_le_EN : ρ ≤ ηEN := by rw [hρdef]; exact min_le_right _ _
  refine ⟨min ηg (min θ₀ ρ), lt_min hηgpos (lt_min hθ₀ hρpos), ?_⟩
  intro η hη hηle Λ D z g hdisc hD hvol hg hg1 hfin hnear
  have hηηg : η ≤ ηg := le_trans hηle (min_le_left _ _)
  have hηθ₀ : η ≤ θ₀ := le_trans hηle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hηρ : η ≤ ρ := le_trans hηle (le_trans (min_le_right _ _) (min_le_right _ _))
  have hηEN : η ≤ ηEN := le_trans hηρ hρ_le_EN
  have hA1 : Submission.Mostow.POActionProp (1 + m) := hAall (1 + m)
  have hI1 : Submission.Mostow.HypIsometryProp (1 + m) := hIall (1 + m)
  have hb1 : POBasic (1 + m) := POBasic.ofProp hA1
  -- a torsion element has a fixed point
  have hfinzp : Finite (Subgroup.zpowers g) := finite_zpowers.mpr hfin
  obtain ⟨p, hp⟩ := fixPoint_of_finite hA1 (Subgroup.zpowers g) hfinzp
  have hgp : g • p = p := hp g (Subgroup.mem_zpowers g)
  -- the elliptic normal form
  obtain ⟨k, m', e, h, R, hRfree, hconj⟩ :=
    elliptic_normal_form (1 + m) hA1 hI1 hAall hIall g ⟨p, hgp⟩
  -- near-identity of the block element
  have hzz : h • (h⁻¹ • z) = z := by
    rw [← hb1.mul_smul h h⁻¹ z, mul_inv_cancel, hb1.one_smul]
  have hnear_h : NearIdAt (h⁻¹ * g * h) (h⁻¹ • z) η :=
    (nearIdAt_conj (1 + m) hA1 hI1 h g (h⁻¹ • z) η).mpr (by rw [hzz]; exact hnear)
  have hnear_big : NearIdAt (e ▸ blk k m' 1 R : PO (1 + m) 1) (h⁻¹ • z) η := by
    have h2 := hnear_h
    rw [hconj] at h2
    exact h2
  have hnear_block : NearIdAt (blk k m' 1 R) (e.symm ▸ (h⁻¹ • z)) η :=
    nearIdAt_cast e (blk k m' 1 R) (h⁻¹ • z) η hnear_big
  -- parity: the normal dimension is even
  have hm'even : Even m' :=
    hEN k m' (hAall k) (hIall k) (hAall (k + m')) (hIall (k + m')) R (e.symm ▸ (h⁻¹ • z))
      hRfree (tnidg_nearIdAt_mono hnear_block hηEN)
  have hkodd : Odd k := by
    have hsum : Odd (k + m') := by rw [e]; exact hev.one_add
    exact (Nat.odd_add.mp hsum).mpr hm'even
  rcases eq_or_ne k 1 with hk1 | hk1
  · -- the desired conclusion
    subst hk1
    exact tnidg_concl_of_block e R hRfree h g hconj
  · -- a higher-dimensional stratum is excluded by the gap hypothesis
    have hk3 : 3 ≤ k := by
      obtain ⟨t, ht⟩ := hkodd.exists_bit1
      have ht0 : t ≠ 0 := by
        intro h0
        exact hk1 (by rw [ht, h0]; norm_num)
      have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
      omega
    have hm'pos : 1 ≤ m' := by
      by_contra hlt
      have hm'0 : m' = 0 := by omega
      subst hm'0
      have hR1 : R = 1 := LinearIsometryEquiv.ext (fun x => Subsingleton.elim _ _)
      have hblk1 : blk k 0 1 R = 1 := by
        rw [hR1, (blk_hom k 0 (hAall k) (hIall k) (hAall (k + 0)) (hIall (k + 0))).2.1]
      have h2 : h⁻¹ * g * h = 1 := by
        rw [hconj, tnidg_cast_eq_one e (blk k 0 1 R) hblk1]
      have hg1' : g = 1 := by
        calc g = h * (h⁻¹ * g * h) * h⁻¹ := by group
          _ = h * 1 * h⁻¹ := by rw [h2]
          _ = 1 := by group
      exact hg1 hg1'
    have hmem :
        (e ▸ blk k m' 1 R : PO (1 + m) 1) ∈ Λ.map (MulAut.conj h⁻¹).toMonoidHom := by
      have hkey : h⁻¹ * g * h = (MulAut.conj h⁻¹).toMonoidHom g := by
        rw [show h⁻¹ * g * h = h⁻¹ * g * (h⁻¹)⁻¹ by rw [inv_inv]]
        exact (MulAut.conj_apply h⁻¹ g).symm
      rw [← hconj, hkey]
      exact Subgroup.mem_map_of_mem _ hg
    have hk2 : 2 ≤ k := by omega
    have hgapconcl := tnidg_gapBlock m hAall hIall θ₀ c α hgap k m' e hk2 hm'pos Λ hdisc D hD
      R hRfree h (h⁻¹ • z) η hη hηθ₀ hmem hnear_big
    have hfin2 : ENNReal.ofReal (c * η ^ (-α)) ≤ ENNReal.ofReal V := le_trans hgapconcl hvol
    exact absurd hfin2 (not_le.mpr (hηgbig η hη hηηg))


end

end Work.Mostow
