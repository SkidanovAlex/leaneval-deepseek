import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.StabHoroForm
import Submission.Work.Mostow.margulisCuspDefs
import Submission.Work.Mostow.margulisPair
import Submission.Work.Mostow.parabolicCommuteFix
import Submission.Work.Mostow.Margulis.nearId_conj_power_parametric
import Submission.Work.Mostow.Margulis.commSeqBase
import Submission.Work.Mostow.Margulis.exists_pow_near_fix_zero
import Submission.Work.Mostow.Margulis.near1_conj_pow
import Submission.Work.Mostow.Margulis.exists_boost_near

/-!
# `Work.Mostow.margulisCuspV2`

The Margulis/Zassenhaus lemma in the form the cusp theory needs: for every `R` there is `ε > 0`
such that in any discrete subgroup `Γ ≤ PO(n,1)`, if a parabolic `q ∈ Γ` with boundary fixed point
`ξ ∈ Sph n` moves a point `u` by less than `ε`, then every `δ ∈ Γ` moving `u` by at most `R` also
fixes `ξ`.

Proof (Zassenhaus commutator argument):

* `Work.Mostow.Margulis.nearId_conj_power_parametric` produces `h` with `h • 0 = u` and a power
  `q ^ j` (`0 < j ≤ N`) whose conjugate `h⁻¹ q ^ j h` has a matrix representative `A` within `η`
  of the identity;
* the conjugated group `Γ' = h⁻¹ Γ h` is discrete; `Work.Mostow.Margulis.Snap.discrete_gap` gives an
  entrywise radius `r` below which a matrix representing an element of `Γ'` is trivial;
* the iterated commutators of `h⁻¹ δ h` with `a = h⁻¹ q ^ j h` shrink geometrically
  (`Work.Mostow.mc_commSeq_shrink`), so one of them is `r`-close to `1`, hence trivial;
* running the commutator sequence backwards (`Work.Mostow.mc_commFixBack`, using that a parabolic
  element has at most one boundary fixed point) gives `bd (h⁻¹ δ h) (bd h⁻¹ ξ) = bd h⁻¹ ξ`, i.e.
  `bd δ ξ = ξ`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Boundary-action bookkeeping -/

lemma mc_bdMul (hA : POActionProp n) (g h : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd (g * h) ξ = bd g (bd h ξ) := hA.2.2.2.2.2.2.2.2.2.1 g h ξ hξ

lemma mc_bdInv (hA : POActionProp n) (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd g⁻¹ (bd g ξ) = ξ := by
  rw [← mc_bdMul hA g⁻¹ g hξ, inv_mul_cancel, hA.2.2.2.2.2.2.2.2.1 ξ hξ]

lemma mc_bdBdInv (hA : POActionProp n) (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd g (bd g⁻¹ ξ) = ξ := by
  have h := mc_bdInv hA g⁻¹ hξ
  rwa [inv_inv] at h

lemma mc_bdSph (hA : POActionProp n) (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd g ξ ∈ Sph n := hA.2.2.2.2.2.2.2.1 g ξ hξ

/-- The sheet-preserving lift of `g` projects back to `g`. -/
lemma mc_ToO_coe (hA : POActionProp n) (g : PO n 1) : (ToO g : PO n 1) = g := by
  rcases Submission.Mostow.Hyper.tsign_eq_one_or (Quotient.out g) with ht | ht
  · have h1 : ToO g = Quotient.out g := by
      apply O1.mat_injective
      rw [mat_ToO, LambdaMat, ht, one_smul]
    rw [h1, QuotientGroup.out_eq']
  · have h1 : ToO g = -(Quotient.out g) := by
      apply O1.mat_injective
      rw [mat_ToO, LambdaMat, ht, mat_neg]
      simp
    rw [h1]
    have hneg : ((-1 : O1 n) : PO n 1) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact (hA.1 (-1)).2 (Or.inr rfl)
    have hsp : (-(Quotient.out g) : O1 n) = (-1 : O1 n) * Quotient.out g := by
      rw [neg_one_mul]
    rw [hsp, QuotientGroup.mk_mul, hneg, one_mul]
    exact QuotientGroup.out_eq' g

/-- The inverse of a parabolic element is parabolic. -/
lemma mc_isParabolic_inv (hA : POActionProp n) (hI : HypIsometryProp n) {g : PO n 1}
    (hg : IsParabolic g) : IsParabolic g⁻¹ := by
  refine ⟨?_, ?_⟩
  · intro u hu
    have h := congrArg (fun x : E n => g • x) hu
    rw [← hA.2.2.2.2.1 g g⁻¹ u, mul_inv_cancel, hA.2.2.2.1] at h
    exact hg.1 u h.symm
  · intro ε hε
    obtain ⟨u, hu⟩ := hg.2 ε hε
    refine ⟨g • u, ?_⟩
    have h1 : hdist (g • u) (g⁻¹ • (g • u)) = hdist (g • u) u := by
      rw [← hA.2.2.2.2.1 g⁻¹ g u, inv_mul_cancel, hA.2.2.2.1]
    rw [h1, ← hI.2.1 u (g • u)]
    exact hu

/-- If `g` is parabolic with boundary fixed point `ξ` and `g * c * g⁻¹ * c⁻¹` also fixes `ξ`,
then `c` fixes `ξ`: uniqueness of the boundary fixed point of a parabolic element. -/
theorem mc_commFixBack (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (g c : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) (hg : IsParabolic g) (hgξ : bd g ξ = ξ)
    (hw : bd (g * c * g⁻¹ * c⁻¹) ξ = ξ) : bd c ξ = ξ := by
  have hginv : IsParabolic g⁻¹ := mc_isParabolic_inv hA hI hg
  have hgξinv : bd g⁻¹ ξ = ξ := by
    have h := mc_bdInv hA g hξ
    rwa [hgξ] at h
  have hwA : bd g (bd c (bd g⁻¹ (bd c⁻¹ ξ))) = ξ := by
    have h1 : bd (g * c * g⁻¹ * c⁻¹) ξ = bd g (bd c (bd g⁻¹ (bd c⁻¹ ξ))) := by
      rw [mc_bdMul hA (g * c * g⁻¹) c⁻¹ hξ,
        mc_bdMul hA (g * c) g⁻¹ (mc_bdSph hA c⁻¹ hξ),
        mc_bdMul hA g c (mc_bdSph hA g⁻¹ (mc_bdSph hA c⁻¹ hξ))]
    rw [← h1]
    exact hw
  have hB : bd c (bd g⁻¹ (bd c⁻¹ ξ)) = ξ := by
    have h := congrArg (bd g⁻¹) hwA
    rw [mc_bdInv hA g (mc_bdSph hA c (mc_bdSph hA g⁻¹ (mc_bdSph hA c⁻¹ hξ)))] at h
    rw [hgξinv] at h
    exact h
  have hC : bd g⁻¹ (bd c⁻¹ ξ) = bd c⁻¹ ξ := by
    have h := congrArg (bd c⁻¹) hB
    rw [mc_bdInv hA c (mc_bdSph hA g⁻¹ (mc_bdSph hA c⁻¹ hξ))] at h
    exact h
  have hψ : ξ = bd c⁻¹ ξ :=
    pcf_parabolic_fixed_unique hA hI g⁻¹ hginv ξ (bd c⁻¹ ξ) hξ (mc_bdSph hA c⁻¹ hξ) hgξinv hC
  calc bd c ξ = bd c (bd c⁻¹ ξ) := by rw [← hψ]
    _ = ξ := mc_bdBdInv hA c hξ

/-- Running the iterated commutator sequence backwards: if `a` is parabolic with boundary fixed
point `Ξ` and the `K`-th iterated commutator of `d₀` with `a` is trivial, then `d₀` fixes `Ξ`. -/
lemma mc_commSeq_backward {a d₀ : PO n 1} {Ξ : E n} (hA : POActionProp n) (hI : HypIsometryProp n)
    (hΞ : Ξ ∈ Sph n) (hpar : IsParabolic a) (hfix : bd a Ξ = Ξ) {K : ℕ}
    (hK : Margulis.Snap.commSeqG a d₀ K = 1) : bd d₀ Ξ = Ξ := by
  have hstep : ∀ e : PO n 1, bd (a * e * a⁻¹ * e⁻¹) Ξ = Ξ → bd e Ξ = Ξ :=
    fun e he => mc_commFixBack n hA hI a e Ξ hΞ hpar hfix he
  have hback : ∀ k : ℕ, bd (Margulis.Snap.commSeqG a d₀ (K - k)) Ξ = Ξ := by
    intro k
    induction k with
    | zero =>
        rw [Nat.sub_zero, hK]
        exact hA.2.2.2.2.2.2.2.2.1 Ξ hΞ
    | succ k ih =>
        rcases Nat.eq_zero_or_pos (K - k) with h0 | hpos
        · have h2 : K - (k + 1) = 0 := by omega
          rw [h0] at ih
          rw [h2]
          exact ih
        · have h2 : K - k = (K - k - 1) + 1 := by omega
          have h3 : K - (k + 1) = K - k - 1 := by omega
          rw [h2, Margulis.Snap.commSeqG_succ] at ih
          rw [h3]
          exact hstep (Margulis.Snap.commSeqG a d₀ (K - k - 1)) ih
  have h := hback K
  rw [Nat.sub_self] at h
  simpa using h


/-- **The contraction estimate** (two-radius form): if `A` has small defect `η` and `B` has defect
at most `C`, then the iterated commutators `commSeq A B j` have defect at most `(1/2)^j * b`. -/
lemma mc_commSeq_shrink (A B : O1 n) {η b C : ℝ}
    (hA : Near1 A η) (hη0 : 0 ≤ η) (hB : Near1 B b) (hb0 : 0 ≤ b) (hbC : b ≤ C)
    (hC0 : 0 ≤ C) (hsmall : 2 * (msz n) ^ 3 * η * (1 + η) * (1 + C) ≤ 1 / 2) (j : ℕ) :
    Near1 (Margulis.Snap.commSeq A B j) ((1 / 2 : ℝ) ^ j * b) := by
  have hm0 : (0 : ℝ) ≤ msz n := msz_nonneg n
  induction j with
  | zero => simpa using hB
  | succ j ih =>
    rw [Margulis.Snap.commSeq_succ]
    have hs0 : 0 ≤ (1 / 2 : ℝ) ^ j * b := by positivity
    have hsC : (1 / 2 : ℝ) ^ j * b ≤ C := by
      have h1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hstep := Margulis.Snap.near1_commutator_gen hA ih
    refine Margulis.Snap.near1_mono hstep ?_
    have hkey : 2 * (msz n) ^ 3 * η * ((1 / 2 : ℝ) ^ j * b) * (1 + η)
        * (1 + (1 / 2 : ℝ) ^ j * b) ≤ (1 / 2) * ((1 / 2 : ℝ) ^ j * b) := by
      have h1 : 2 * (msz n) ^ 3 * η * (1 + η) * (1 + (1 / 2 : ℝ) ^ j * b) ≤ 1 / 2 := by
        have h2 : 0 ≤ 2 * (msz n) ^ 3 * η * (1 + η) := by positivity
        have h3 : 1 + (1 / 2 : ℝ) ^ j * b ≤ 1 + C := by linarith
        nlinarith [mul_le_mul_of_nonneg_left h3 h2]
      calc 2 * (msz n) ^ 3 * η * ((1 / 2 : ℝ) ^ j * b) * (1 + η)
            * (1 + (1 / 2 : ℝ) ^ j * b)
          = ((1 / 2 : ℝ) ^ j * b) * (2 * (msz n) ^ 3 * η * (1 + η)
            * (1 + (1 / 2 : ℝ) ^ j * b)) := by ring
        _ ≤ ((1 / 2 : ℝ) ^ j * b) * (1 / 2) := mul_le_mul_of_nonneg_left h1 hs0
        _ = (1 / 2) * ((1 / 2 : ℝ) ^ j * b) := by ring
    have hfin : (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ j * b) = (1 / 2 : ℝ) ^ (j + 1) * b := by
      rw [pow_succ]; ring
    linarith [hkey, hfin]

theorem margulisCuspV2 (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n) : ∀ R : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)), IsDiscrete (SetLike.coe Γ) → ∀ (u ξ : Submission.Mostow.E n) (q δ : Γ), Submission.Mostow.IsParabolic (q : LeanEval.Geometry.MostowRigidity.PO n 1) → ξ ∈ Submission.Mostow.Sph n → Submission.Mostow.bd (q : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ → Submission.Mostow.hdist u ((q : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε → Submission.Mostow.hdist u ((δ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) ≤ R → Submission.Mostow.bd (δ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ := by
  intro R
  set b₀ : ℝ := Real.cosh R + 1 with hb₀def
  have hb₀nn : 0 ≤ b₀ := by
    rw [hb₀def]
    have h := Real.one_le_cosh R
    linarith
  have hb₀pos : 0 < b₀ := by
    rw [hb₀def]
    have h := Real.one_le_cosh R
    linarith
  have hmszpos : (0 : ℝ) < msz n := lt_of_lt_of_le zero_lt_one (one_le_msz n)
  set η : ℝ := min (1 / 2) (1 / (32 * (msz n) ^ 3 * (1 + b₀))) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    exact lt_min (by norm_num) (by positivity)
  have hηnn : 0 ≤ η := le_of_lt hηpos
  have hηhalf : η ≤ 1 / 2 := by rw [hηdef]; exact min_le_left _ _
  have hηle : η ≤ 1 / (32 * (msz n) ^ 3 * (1 + b₀)) := by
    rw [hηdef]; exact min_le_right _ _
  have hkey : η * (32 * (msz n) ^ 3 * (1 + b₀)) ≤ 1 := by
    have hd : (0 : ℝ) < 32 * (msz n) ^ 3 * (1 + b₀) := by positivity
    have h := mul_le_mul_of_nonneg_right hηle (le_of_lt hd)
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hd)] at h
    exact h
  have hsmall : 2 * (msz n) ^ 3 * η * (1 + η) * (1 + b₀) ≤ 1 / 2 := by
    have h1 : (1 + η) ≤ 3 / 2 := by linarith
    have hnn : (0 : ℝ) ≤ 2 * (msz n) ^ 3 * η * (1 + b₀) := by positivity
    have h2 : 2 * (msz n) ^ 3 * η * (1 + η) * (1 + b₀)
        ≤ 2 * (msz n) ^ 3 * η * (3 / 2) * (1 + b₀) := by
      calc 2 * (msz n) ^ 3 * η * (1 + η) * (1 + b₀)
          = (2 * (msz n) ^ 3 * η * (1 + b₀)) * (1 + η) := by ring
        _ ≤ (2 * (msz n) ^ 3 * η * (1 + b₀)) * (3 / 2) := mul_le_mul_of_nonneg_left h1 hnn
        _ = 2 * (msz n) ^ 3 * η * (3 / 2) * (1 + b₀) := by ring
    have h3 : 2 * (msz n) ^ 3 * η * (3 / 2) * (1 + b₀) ≤ 1 / 2 := by
      have he : 2 * (msz n) ^ 3 * η * (3 / 2) * (1 + b₀)
          = (η * (32 * (msz n) ^ 3 * (1 + b₀))) * (3 / 32) := by ring
      rw [he]
      nlinarith [hkey]
    linarith [h2, h3]
  obtain ⟨N, ε, hεpos, hNpos, hpid⟩ := Margulis.nearId_conj_power_parametric n hA hI η hηpos
  refine ⟨ε, hεpos, ?_⟩
  intro Γ hdisc u ξ q δq hqpar hξ hqξ hqu hdu
  by_cases hR : 0 ≤ R
  · obtain ⟨h, hh0, hshort⟩ := hpid u
    obtain ⟨j, hjpos, hjN, A, hAcoe, hAnear⟩ := hshort (q : PO n 1) hqu
    set Ξ : E n := bd h⁻¹ ξ with hΞdef
    have hΞmem : Ξ ∈ Sph n := by rw [hΞdef]; exact mc_bdSph hA h⁻¹ hξ
    set a : PO n 1 := h⁻¹ * (q : PO n 1) ^ j * h with hadef
    have hAcoe' : (A : PO n 1) = a := by rw [hadef]; exact hAcoe
    have hapar : IsParabolic a := by
      rw [hadef]
      have hqj : IsParabolic ((q : PO n 1) ^ j) :=
        pcf_parabolic_pow hA hI (q : PO n 1) hqpar j hjpos
      have hconj := isParabolic_conj hA hI (h⁻¹ : PO n 1) ((q : PO n 1) ^ j) hqj
      simpa using hconj
    have hafix : bd a Ξ = Ξ := by
      have hmem1 : bd h Ξ ∈ Sph n := mc_bdSph hA h hΞmem
      have h1 : bd a Ξ = bd (h⁻¹ * (q : PO n 1) ^ j) (bd h Ξ) := by
        rw [hadef]
        exact mc_bdMul hA (h⁻¹ * (q : PO n 1) ^ j) h hΞmem
      have h2 : bd (h⁻¹ * (q : PO n 1) ^ j) (bd h Ξ)
          = bd h⁻¹ (bd ((q : PO n 1) ^ j) (bd h Ξ)) :=
        mc_bdMul hA h⁻¹ ((q : PO n 1) ^ j) hmem1
      have h3 : bd h Ξ = ξ := by
        rw [hΞdef]
        exact mc_bdBdInv hA h hξ
      have h4 : bd ((q : PO n 1) ^ j) (bd h Ξ) = ξ := by
        rw [h3]
        exact pcf_bd_pow_fixed hA (q : PO n 1) ξ hξ hqξ j
      rw [h1, h2, h4]
    set d₀ : PO n 1 := h⁻¹ * (δq : PO n 1) * h with hd₀def
    have hd₀short : hdist (0 : E n) (d₀ • (0 : E n)) ≤ R := by
      have hu0 : h⁻¹ • u = 0 := by
        rw [← hh0, ← hA.2.2.2.2.1 h⁻¹ h (0 : E n), inv_mul_cancel, hA.2.2.2.1]
      have h1 : d₀ • (0 : E n) = h⁻¹ • ((δq : PO n 1) • u) := by
        rw [hd₀def, hA.2.2.2.2.1, hA.2.2.2.2.1, hh0]
      rw [h1]
      have h2 : hdist (0 : E n) (h⁻¹ • ((δq : PO n 1) • u))
          = hdist u ((δq : PO n 1) • u) := by
        rw [← hu0, hI.2.2.2.2.2.2.1 h⁻¹ u ((δq : PO n 1) • u)]
      rw [h2]
      exact hdu
    have hNearD : Near1 (ToO d₀) b₀ := by
      rw [hb₀def]
      exact Near1_ToO_of_hdist hR hd₀short
    set Γ' : Subgroup (PO n 1) := Γ.map (MulAut.conj h⁻¹).toMonoidHom with hΓ'def
    have hdisc' : IsDiscrete (SetLike.coe Γ') := by
      rw [hΓ'def]
      exact isDiscrete_map_conj hdisc h
    have hmemA : a ∈ Γ' := by
      rw [hΓ'def, hadef]
      refine Subgroup.mem_map.mpr ⟨(q : PO n 1) ^ j, Γ.pow_mem q.2 j, ?_⟩
      simp [MulAut.conj_apply]
    have hmemD : d₀ ∈ Γ' := by
      rw [hΓ'def, hd₀def]
      refine Subgroup.mem_map.mpr ⟨(δq : PO n 1), δq.2, ?_⟩
      simp [MulAut.conj_apply]
    obtain ⟨r, hrpos, hrhalf, hgap⟩ := Margulis.Snap.discrete_gap n hA Γ' hdisc'
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ((1 / 2 : ℝ) ^ K) * b₀ < r := by
      obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (x := r / b₀) (y := (1 / 2 : ℝ))
        (div_pos hrpos hb₀pos) (by norm_num)
      refine ⟨K, ?_⟩
      have h := mul_lt_mul_of_pos_right hK hb₀pos
      rwa [div_mul_cancel₀ r (ne_of_gt hb₀pos)] at h
    have hKnear : Near1 (Margulis.Snap.commSeq A (ToO d₀) K) ((1 / 2 : ℝ) ^ K * b₀) :=
      mc_commSeq_shrink A (ToO d₀) hAnear hηnn hNearD hb₀nn le_rfl hb₀nn hsmall K
    have hKnearr : Near1 (Margulis.Snap.commSeq A (ToO d₀) K) r :=
      Margulis.Snap.near1_mono hKnear (le_of_lt hK)
    have hmem_c : ((Margulis.Snap.commSeq A (ToO d₀) K : O1 n) : PO n 1) ∈ Γ' :=
      Margulis.Snap.commSeq_mem (hA := by rw [hAcoe']; exact hmemA)
        (hB := by rw [mc_ToO_coe hA d₀]; exact hmemD) K
    have hc_one : Margulis.Snap.commSeq A (ToO d₀) K = 1 :=
      hgap (Margulis.Snap.commSeq A (ToO d₀) K) hmem_c hKnearr
    have hG_one : Margulis.Snap.commSeqG a d₀ K = 1 := by
      have h := Margulis.Snap.commSeq_coe (A := A) (B := ToO d₀) K
      rw [hc_one] at h
      rw [show ((1 : O1 n) : PO n 1) = 1 from rfl, hAcoe', mc_ToO_coe hA d₀] at h
      exact h.symm
    have hd₀fix : bd d₀ Ξ = Ξ := mc_commSeq_backward hA hI hΞmem hapar hafix hG_one
    have hd₀fix' : bd (h⁻¹ * (δq : PO n 1) * h) (bd h⁻¹ ξ) = bd h⁻¹ ξ := by
      rw [hd₀def, hΞdef] at hd₀fix
      exact hd₀fix
    have hmem1 : bd h⁻¹ ξ ∈ Sph n := mc_bdSph hA h⁻¹ hξ
    have hmem2 : bd (δq : PO n 1) ξ ∈ Sph n := mc_bdSph hA (δq : PO n 1) hξ
    have he1 : bd (h⁻¹ * (δq : PO n 1) * h) (bd h⁻¹ ξ)
        = bd h⁻¹ (bd (δq : PO n 1) (bd h (bd h⁻¹ ξ))) := by
      rw [mc_bdMul hA (h⁻¹ * (δq : PO n 1)) h hmem1,
        mc_bdMul hA h⁻¹ (δq : PO n 1) (mc_bdSph hA h hmem1)]
    have he2 : bd h (bd h⁻¹ ξ) = ξ := mc_bdBdInv hA h hξ
    have hcore : bd h⁻¹ (bd (δq : PO n 1) ξ) = bd h⁻¹ ξ := by
      have key : bd (δq : PO n 1) ξ = bd (δq : PO n 1) (bd h (bd h⁻¹ ξ)) := by
        rw [he2]
      rw [key, ← he1]
      exact hd₀fix'
    have hfinal : bd (δq : PO n 1) ξ = ξ := by
      have h2 := congrArg (bd h) hcore
      have hl : bd h (bd h⁻¹ (bd (δq : PO n 1) ξ)) = bd (δq : PO n 1) ξ := by
        rw [← mc_bdMul hA h h⁻¹ hmem2, mul_inv_cancel,
          hA.2.2.2.2.2.2.2.2.1 _ hmem2]
      rw [hl, he2] at h2
      exact h2
    exact hfinal
  · have h0 : 0 ≤ hdist u ((δq : PO n 1) • u) := hI.1 u _
    linarith

end

end Work.Mostow
