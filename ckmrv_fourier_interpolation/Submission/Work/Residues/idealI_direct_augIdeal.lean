/-
# Directness of `(T-I)²R + S(T-I)²R` modulo the collapse ideal `(z-1)R`

The transfer `Xi : ℂ[SL(2,ℤ)] →ₐ[ℂ] ℂ[PSL(2,ℤ)]` (`Work.Residues.XiTransfer`) has kernel
exactly `augIdeal = (z-1)R`, `z = -I`.  Hence an identity in `R = ℂ[SL(2,ℤ)]` modulo
`augIdeal` is an identity in `ℂ[Γ]`, `Γ = ⟨S,T ∣ S² = (ST)³ = 1⟩`, and the statement to prove
is the directness of `(T-I)²·ℂ[Γ] + S(T-I)²·ℂ[Γ]` (CKMRV, Proposition 3.9 for `𝓘`).

Two routes are formalised here:

* `idealI_direct_augIdeal` reduces to the directness in the free product algebra
  `ℂ[ℤ/2 ∗ ℤ/3] = ℂ[PSL(2,ℤ)]`: the transfer `Xi` carries the hypothesis to the identity
  `(T-1)²·Xi A + S(T-1)²·Xi B = 0` in `ℂ[Γ]`, which the algebra isomorphism
  `ℂ[Γ] ≃ₐ[ℂ] ℂ[ℤ/2 ∗ ℤ/3]` (`groupRing_direct_of_FP`) sends to the corresponding identity
  there; that identity is `Work.FreeProduct.idealI_direct` (CKMRV Proposition 3.9 for `𝓘`).

Also contained here: `IM_idealImDirect`, an independent proof of the `𝓘₋` half
`(T-1)²u = (X-1)w → u = 0` (via the paper's Lemma 3.7 and the intersection
`(X-1)·ℂ[FP] ∩ (Y-1)·ℂ[FP] = 0`), the assembly `fp_direct_of_halves` of the two halves, and
the equivalence `IM_ipDirect_of_torsion` between the two forms of the `𝓘₊` half.
-/
import Mathlib
import Submission.Work.Residues.Basic
import Submission.Work.Residues.XiTransfer
import Submission.Work.FreeProduct.claim_L3
import Submission.Work.FreeProduct.IdealIpDirect

open scoped MonoidAlgebra

namespace Work.Residues

open Work.Kernels
open Work.FreeProduct
open Work.Modular.PresGroup

/-! ## The transfer `Xi` kills exactly `augIdeal` -/

lemma Xi_eq_zero_of_mem {x : R} (hx : x ∈ augIdeal) : Xi x = 0 :=
  LinearMap.mem_ker.mp (augIdeal_le_ker_Xi hx)

lemma mem_augIdeal_of_Xi_eq_zero {x : R} (hx : Xi x = 0) : x ∈ augIdeal :=
  ker_Xi_le_augIdeal (LinearMap.mem_ker.mpr hx)

/-! ## The `±1` eigenspaces of the involution `X = S` in `ℂ[ℤ/2 ∗ ℤ/3]`

`ker (X+1) = (X-1)·RR` and `ker (1-X) = (X+1)·RR`: an element fixed by `X` (respectively
anti-fixed) is a multiple of `1+X` (respectively of `X-1`). -/

lemma ker_one_add_X (v : Work.FreeProduct.RR) (h : (Work.FreeProduct.X + 1) * v = 0) :
    ∃ w, v = (Work.FreeProduct.X - 1) * w := by
  have hXv : Work.FreeProduct.X * v = -v := by
    have h' : Work.FreeProduct.X * v + v = 0 := by simpa [add_mul, one_mul] using h
    exact eq_neg_of_add_eq_zero_left h'
  refine ⟨-(2⁻¹ : ℂ) • v, ?_⟩
  rw [sub_mul, one_mul, mul_smul_comm, hXv]
  simp only [neg_smul, smul_neg, neg_neg, sub_neg_eq_add]
  rw [← add_smul]
  norm_num

lemma ker_one_sub_X (v : Work.FreeProduct.RR) (h : (1 - Work.FreeProduct.X) * v = 0) :
    ∃ w, v = (Work.FreeProduct.X + 1) * w := by
  have hXv : Work.FreeProduct.X * v = v := by
    have h' : v - Work.FreeProduct.X * v = 0 := by simpa [sub_mul, one_mul] using h
    exact (sub_eq_zero.mp h').symm
  refine ⟨(2⁻¹ : ℂ) • v, ?_⟩
  rw [add_mul, one_mul, mul_smul_comm, hXv]
  rw [← add_smul]
  norm_num

/-! ## Assembly of the two halves in `ℂ[ℤ/2 ∗ ℤ/3]` -/

/-- The two "half" directness statements imply the directness of `𝓘` in the free product
algebra. -/
theorem fp_direct_of_halves
    (hIm : ∀ {u w : Work.FreeProduct.RR},
      (Work.FreeProduct.TT - 1) ^ 2 * u = (Work.FreeProduct.X - 1) * w → u = 0)
    (hIp : ∀ {u w : Work.FreeProduct.RR},
      (Work.FreeProduct.TT - 1) ^ 2 * u = (Work.FreeProduct.X + 1) * w → u = 0)
    {a b : Work.FreeProduct.RR}
    (h : (Work.FreeProduct.TT - 1) ^ 2 * a
      + Work.FreeProduct.X * (Work.FreeProduct.TT - 1) ^ 2 * b = 0) : a = 0 ∧ b = 0 := by
  set A : Work.FreeProduct.RR := (Work.FreeProduct.TT - 1) ^ 2 with hA
  have h1 : A * a = -(Work.FreeProduct.X * A * b) := by
    rw [eq_neg_iff_add_eq_zero]
    calc A * a + Work.FreeProduct.X * A * b
        = (Work.FreeProduct.TT - 1) ^ 2 * a
            + Work.FreeProduct.X * (Work.FreeProduct.TT - 1) ^ 2 * b := by rw [hA]
      _ = 0 := h
  have h2 : Work.FreeProduct.X * A * a = -(A * b) := by
    calc Work.FreeProduct.X * A * a = Work.FreeProduct.X * (A * a) := by rw [mul_assoc]
      _ = Work.FreeProduct.X * (-(Work.FreeProduct.X * A * b)) := by rw [h1]
      _ = -(Work.FreeProduct.X * (Work.FreeProduct.X * A * b)) := by rw [mul_neg]
      _ = -((Work.FreeProduct.X * Work.FreeProduct.X) * A * b) := by
            rw [← mul_assoc, ← mul_assoc]
      _ = -(A * b) := by rw [Work.FreeProduct.X_mul_X, one_mul]
  have hsum : (Work.FreeProduct.X + 1) * (A * (a + b)) = 0 := by
    have e : (Work.FreeProduct.X + 1) * (A * (a + b))
        = (A * a + Work.FreeProduct.X * A * a) + (A * b + Work.FreeProduct.X * A * b) := by
      noncomm_ring
    rw [e, h1, h2]; abel
  have hdiff : (1 - Work.FreeProduct.X) * (A * (a - b)) = 0 := by
    have e : (1 - Work.FreeProduct.X) * (A * (a - b))
        = (A * a - Work.FreeProduct.X * A * a) - (A * b - Work.FreeProduct.X * A * b) := by
      noncomm_ring
    rw [e, h1, h2]; abel
  have hab : a + b = 0 := by
    obtain ⟨w, hw⟩ := ker_one_add_X (A * (a + b)) hsum
    exact hIm hw
  have hdif : a - b = 0 := by
    obtain ⟨w, hw⟩ := ker_one_sub_X (A * (a - b)) hdiff
    exact hIp hw
  have ha : a = 0 := by
    have h3 : a + b + (a - b) = (2 : ℂ) • a := by rw [two_smul]; abel
    rw [hab, hdif, add_zero] at h3
    have h4 := congrArg (fun x => (2 : ℂ)⁻¹ • x) h3.symm
    simpa [smul_smul, show (2 : ℂ) ≠ 0 by norm_num] using h4
  have hb : b = 0 := by
    rw [ha, zero_add] at hab
    exact hab
  exact ⟨ha, hb⟩

/-! ## The transport `ℂ[Γ] → ℂ[ℤ/2 ∗ ℤ/3]` -/

/-- The algebra isomorphism `ℂ[Γ] ≃ₐ[ℂ] ℂ[ℤ/2 ∗ ℤ/3]` carries `tR ↦ TT`. -/
theorem domCongr_tR :
    (MonoidAlgebra.domCongr ℂ ℂ Work.Modular.PresGroup.gammaEquivFP) Work.Modular.tR
      = Work.FreeProduct.TT := by
  rw [Work.Modular.tR, Work.FreeProduct.TT]
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.domCongr_single]
  rw [show Work.Modular.PresGroup.gammaEquivFP Work.Modular.genT = Work.FreeProduct.T from by
    rw [Work.FreeProduct.T, Work.FreeProduct.x, Work.FreeProduct.y]
    exact Work.Modular.PresGroup.toFree_genT]

/-- The algebra isomorphism `ℂ[Γ] ≃ₐ[ℂ] ℂ[ℤ/2 ∗ ℤ/3]` carries `sR ↦ X`. -/
theorem domCongr_sR :
    (MonoidAlgebra.domCongr ℂ ℂ Work.Modular.PresGroup.gammaEquivFP) Work.Modular.sR
      = Work.FreeProduct.X := by
  rw [Work.Modular.sR, Work.FreeProduct.X]
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.domCongr_single]
  rw [show Work.Modular.PresGroup.gammaEquivFP Work.Modular.genS = Work.FreeProduct.x from by
    rw [Work.FreeProduct.x]
    exact Work.Modular.PresGroup.toFree_genS]

/-- The directness in `ℂ[Γ]` follows from the directness in the free product algebra. -/
theorem groupRing_direct_of_FP
    (hFP : ∀ {a b : Work.FreeProduct.RR},
      (Work.FreeProduct.TT - 1) ^ 2 * a
        + Work.FreeProduct.X * (Work.FreeProduct.TT - 1) ^ 2 * b = 0 → a = 0 ∧ b = 0)
    {a b : Work.Modular.GroupRing}
    (h : (Work.Modular.tR - 1) ^ 2 * a + Work.Modular.sR * (Work.Modular.tR - 1) ^ 2 * b
      = 0) : a = 0 ∧ b = 0 := by
  set E := MonoidAlgebra.domCongr ℂ ℂ Work.Modular.PresGroup.gammaEquivFP with hE
  have ht : E Work.Modular.tR = Work.FreeProduct.TT := domCongr_tR
  have hs : E Work.Modular.sR = Work.FreeProduct.X := domCongr_sR
  have hEeq : (Work.FreeProduct.TT - 1) ^ 2 * E a
      + Work.FreeProduct.X * (Work.FreeProduct.TT - 1) ^ 2 * E b = 0 := by
    have h' := congrArg (fun x => E x) h
    simp only [map_add, map_mul, map_pow, map_sub, map_one, ht, hs] at h'
    rw [map_zero] at h'
    exact h'
  obtain ⟨ha, hb⟩ := hFP hEeq
  exact ⟨E.injective (by rw [ha, map_zero]), E.injective (by rw [hb, map_zero])⟩

/-! ## The `𝓘₋` half in the free product algebra

The proof of `(T-1)²u = (X-1)w → u = 0` follows CKMRV: `(T-1)u ∈ μ·ℂ[FP]` (Lemma 3.7),
whence `(Y-1)(T-1)u = 0` and `Work.FreeProduct.claim_L3` finishes.  The paper's Lemma 3.7 uses
the intersection `(X-1)·ℂ[FP] ∩ (Y-1)·ℂ[FP] = 0`, which is proved here by canonicalising modulo
`(X-1)·ℂ[FP]` and comparing the leading coefficient of `μ(X-1)u`.
-/

theorem IM_MU_mul_Y_sub_one : MU * (Y - 1) = 0 := by
  rw [MU, mul_sub, add_mul, add_mul, one_mul, mul_one, Y2_mul_Y, Y_mul_Y]
  abel

/-- A single group element is congruent modulo `(X-1)·RR` to an element whose support is
`NX` (does not start with `x`). -/
theorem IM_exists_nx_single (γ : FP) :
    ∃ a : RR, (X - 1) * MonoidAlgebra.single γ (1 : ℂ) = (X - 1) * a ∧
      (∀ δ ∈ (MonoidAlgebra.coeff a).support, NX δ) := by
  by_cases h : NX γ
  · refine ⟨MonoidAlgebra.single γ 1, rfl, ?_⟩
    intro δ hδ
    have h1 : δ = γ := by
      have := Finsupp.support_single_subset hδ
      simpa using this
    rwa [h1]
  · have hf : (Monoid.CoprodI.Word.equiv γ).fstIdx = some false := by
      by_contra hne
      exact h hne
    obtain ⟨γ', hγ', hNX'⟩ := Work.FreeProduct.exists_X_dcomp γ hf
    refine ⟨-MonoidAlgebra.single γ' 1, ?_, ?_⟩
    · have h1 : X * MonoidAlgebra.single γ' (1 : ℂ) = MonoidAlgebra.single γ (1 : ℂ) := by
        rw [X, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one, ← hγ']
      have h2 : (X - 1) * (X * MonoidAlgebra.single γ' (1 : ℂ))
          = -((X - 1) * MonoidAlgebra.single γ' (1 : ℂ)) := by
        calc (X - 1) * (X * MonoidAlgebra.single γ' (1 : ℂ))
            = ((X - 1) * X) * MonoidAlgebra.single γ' (1 : ℂ) := by rw [mul_assoc]
          _ = (X * X - 1 * X) * MonoidAlgebra.single γ' (1 : ℂ) := by rw [sub_mul]
          _ = (1 - X) * MonoidAlgebra.single γ' (1 : ℂ) := by rw [X_mul_X, one_mul]
          _ = 1 * MonoidAlgebra.single γ' (1 : ℂ)
                - X * MonoidAlgebra.single γ' (1 : ℂ) := by rw [sub_mul]
          _ = MonoidAlgebra.single γ' (1 : ℂ)
                - X * MonoidAlgebra.single γ' (1 : ℂ) := by rw [one_mul]
          _ = -(X * MonoidAlgebra.single γ' (1 : ℂ)
                - MonoidAlgebra.single γ' (1 : ℂ)) := by rw [← neg_sub]
          _ = -((X - 1) * MonoidAlgebra.single γ' (1 : ℂ)) := by rw [sub_mul, one_mul]
      rw [← h1, h2, mul_neg]
    · intro δ hδ
      rw [MonoidAlgebra.coeff_neg, Finsupp.support_neg] at hδ
      have h1 : δ = γ' := by
        have := Finsupp.support_single_subset hδ
        simpa using this
      rwa [h1]

/-- Every element of `RR` is congruent modulo `(X-1)·RR` to an element whose support is `NX`. -/
theorem IM_exists_nx_mul (u : RR) :
    ∃ u' : RR, (X - 1) * u = (X - 1) * u' ∧
      (∀ δ ∈ (MonoidAlgebra.coeff u').support, NX δ) := by
  induction u using MonoidAlgebra.induction_on with
  | of γ =>
      obtain ⟨a, ha, haNX⟩ := IM_exists_nx_single γ
      exact ⟨a, by rw [MonoidAlgebra.of_apply, ha], haNX⟩
  | add u v hu hv =>
      obtain ⟨u', hu1, hu2⟩ := hu
      obtain ⟨v', hv1, hv2⟩ := hv
      refine ⟨u' + v', ?_, ?_⟩
      · rw [mul_add, hu1, hv1, mul_add]
      · intro δ hδ
        rcases Finset.mem_union.mp (Finsupp.support_add hδ) with h | h
        · exact hu2 δ h
        · exact hv2 δ h
  | smul c u hu =>
      obtain ⟨u', hu1, hu2⟩ := hu
      refine ⟨c • u', ?_, ?_⟩
      · rw [mul_smul_comm, hu1, mul_smul_comm]
      · intro δ hδ
        refine hu2 δ ?_
        rw [Finsupp.mem_support_iff] at hδ ⊢
        intro h0
        exact hδ (by simp [h0])

/-! ## The leading coefficient of `μ (X-1) u` -/

theorem IM_coeff_eq_zero_of_elen_gt {u : RR} {γ δ : FP}
    (hmax : ∀ ε ∈ (MonoidAlgebra.coeff u).support, elen ε ≤ elen γ)
    (h : elen γ < elen δ) : MonoidAlgebra.coeff u δ = 0 := by
  by_contra hne
  have hδ : δ ∈ (MonoidAlgebra.coeff u).support := Finsupp.mem_support_iff.mpr hne
  exact absurd (hmax δ hδ) (not_le.mpr h)

theorem IM_MU_mul_X_sub_one_eq :
    MU * (X - 1) = Y2 * X + Y * X + X - Y2 - Y - 1 := by
  rw [MU, mul_sub, add_mul, add_mul, one_mul, mul_one]
  abel

theorem IM_coeff_MU_X_sub_one_mul {u : RR} {γ : FP}
    (hγ : γ ∈ (MonoidAlgebra.coeff u).support) (hNX : NX γ)
    (hmax : ∀ ε ∈ (MonoidAlgebra.coeff u).support, elen ε ≤ elen γ) :
    MonoidAlgebra.coeff (MU * (X - 1) * u) (y2 * x * γ) = MonoidAlgebra.coeff u γ := by
  have hY2X : Y2 * X = MonoidAlgebra.of ℂ FP (y2 * x) := by rw [Y2, X, ← map_mul]
  have hYX : Y * X = MonoidAlgebra.of ℂ FP (y * x) := by rw [Y, X, ← map_mul]
  have hX' : X = MonoidAlgebra.of ℂ FP x := rfl
  have hY2' : Y2 = MonoidAlgebra.of ℂ FP y2 := rfl
  have hY' : Y = MonoidAlgebra.of ℂ FP y := rfl
  have hexp : MU * (X - 1) * u
      = (Y2 * X) * u + (Y * X) * u + X * u - Y2 * u - Y * u - u := by
    rw [IM_MU_mul_X_sub_one_eq, sub_mul, sub_mul, sub_mul, add_mul, add_mul, one_mul]
  rw [hexp, MonoidAlgebra.coeff_sub, Finsupp.sub_apply, MonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_add, Finsupp.add_apply,
    hY2X, hYX, hX', hY2', hY', coeff_of_mul, coeff_of_mul, coeff_of_mul, coeff_of_mul,
    coeff_of_mul]
  have g1 : (y2 * x)⁻¹ * (y2 * x * γ) = γ := by rw [inv_mul_cancel_left]
  have g2 : (y * x)⁻¹ * (y2 * x * γ) = x * y * x * γ := by
    rw [mul_inv_rev, x_inv, y_inv]
    calc x * y2 * (y2 * x * γ) = x * (y2 * y2) * (x * γ) := by group
      _ = x * y * (x * γ) := by rw [y2_mul_y2]
      _ = x * y * x * γ := by group
  have g3 : x⁻¹ * (y2 * x * γ) = x * y2 * x * γ := by
    rw [x_inv]
    group
  have g4 : (y2)⁻¹ * (y2 * x * γ) = x * γ := by
    rw [y2_inv]
    calc y * (y2 * x * γ) = y * (y2 * (x * γ)) := by group
      _ = (y * y2) * (x * γ) := by group
      _ = x * γ := by rw [y_mul_y2, one_mul]
  have g5 : y⁻¹ * (y2 * x * γ) = y * x * γ := by
    rw [y_inv]
    calc y2 * (y2 * x * γ) = y2 * (y2 * (x * γ)) := by group
      _ = (y2 * y2) * (x * γ) := by group
      _ = y * (x * γ) := by rw [y2_mul_y2]
      _ = y * x * γ := by group
  have L2 : elen γ < elen (x * y * x * γ) := by rw [elen_xyx_mul hNX]; omega
  have L3 : elen γ < elen (x * y2 * x * γ) := by rw [elen_xy2x_mul hNX]; omega
  have L4 : elen γ < elen (x * γ) := by rw [elen_x_mul hNX]; omega
  have L5 : elen γ < elen (y * x * γ) := by rw [elen_yx_mul hNX]; omega
  have L6 : elen γ < elen (y2 * x * γ) := by rw [elen_y2x_mul hNX]; omega
  rw [g1, g2, g3, g4, g5,
    IM_coeff_eq_zero_of_elen_gt (u := u) (γ := γ) (δ := x * y * x * γ) hmax L2,
    IM_coeff_eq_zero_of_elen_gt (u := u) (γ := γ) (δ := x * y2 * x * γ) hmax L3,
    IM_coeff_eq_zero_of_elen_gt (u := u) (γ := γ) (δ := x * γ) hmax L4,
    IM_coeff_eq_zero_of_elen_gt (u := u) (γ := γ) (δ := y * x * γ) hmax L5,
    IM_coeff_eq_zero_of_elen_gt (u := u) (γ := γ) (δ := y2 * x * γ) hmax L6]
  ring

theorem IM_eq_zero_of_MU_mul_X_sub_one {u : RR}
    (hNX : ∀ δ ∈ (MonoidAlgebra.coeff u).support, NX δ) (h : MU * (X - 1) * u = 0) :
    u = 0 := by
  by_contra hne
  obtain ⟨γ, hγmem, hγmax⟩ := Finset.exists_max_image (MonoidAlgebra.coeff u).support
    (fun γ => elen γ) (support_nonempty_of_ne_zero hne)
  have hcoeff : MonoidAlgebra.coeff (MU * (X - 1) * u) (y2 * x * γ)
      = MonoidAlgebra.coeff u γ :=
    IM_coeff_MU_X_sub_one_mul hγmem (hNX γ hγmem) (fun δ hδ => hγmax δ hδ)
  rw [h] at hcoeff
  simp at hcoeff
  exact (Finsupp.mem_support_iff.mp hγmem) hcoeff.symm

/-! ## The intersection and the `𝓘₋` half -/

theorem IM_inter_eq_zero {V : RR} (hX : ∃ u, V = (X - 1) * u) (hY : ∃ s, V = (Y - 1) * s) :
    V = 0 := by
  obtain ⟨u, rfl⟩ := hX
  obtain ⟨u', hu', hNX⟩ := IM_exists_nx_mul u
  obtain ⟨s, hs⟩ := hY
  have h0 : MU * (X - 1) * u' = 0 := by
    calc MU * (X - 1) * u' = MU * ((X - 1) * u') := by rw [mul_assoc]
      _ = MU * ((X - 1) * u) := by rw [hu']
      _ = MU * ((Y - 1) * s) := by rw [hs]
      _ = MU * (Y - 1) * s := by rw [mul_assoc]
      _ = 0 := by rw [IM_MU_mul_Y_sub_one, zero_mul]
  have huz : u' = 0 := IM_eq_zero_of_MU_mul_X_sub_one hNX h0
  rw [hu', huz, mul_zero]

theorem IM_TT_sub_one_mul_eq : (TT - 1) = (X - 1) * Y + (Y - 1) := by
  rw [← X_mul_Y, sub_mul, one_mul]
  abel

theorem IM_idealImDirect {u w : RR} (h : (TT - 1) ^ 2 * u = (X - 1) * w) : u = 0 := by
  set V : RR := (TT - 1) * u with hV
  have h1 : (TT - 1) * V = (X - 1) * w := by
    rw [hV, ← mul_assoc, ← sq]; exact h
  have hYVmem : ∃ t, (Y - 1) * V = (X - 1) * t := by
    refine ⟨w - Y * V, ?_⟩
    have hsplit : (TT - 1) * V = (X - 1) * (Y * V) + (Y - 1) * V := by
      rw [IM_TT_sub_one_mul_eq, add_mul, mul_assoc]
    have h2 : (Y - 1) * V = (X - 1) * w - (X - 1) * (Y * V) := by
      rw [hsplit] at h1
      rw [← h1]
      abel
    rw [h2, ← mul_sub]
  have hYV0 : (Y - 1) * V = 0 := IM_inter_eq_zero hYVmem ⟨V, rfl⟩
  have hfin : (Y - 1) * (TT - 1) * u = 0 := by
    rw [hV, ← mul_assoc] at hYV0
    exact hYV0
  exact claim_L3 u hfin



/-! ## Converting the torsion form of the `𝓘₊` statement into the equation form

`(1-X)(TT-1) = -((1-X)(1+Y))`, so the two hypotheses `(TT-1)²u = (X+1)w` and
`(1-X)(1+Y)(TT-1)u = 0` are equivalent; this is used to switch between the two forms of the
`𝓘₊` half of CKMRV Proposition 3.9.
-/

theorem IM_one_sub_X_mul_TT_sub_one : (1 - X) * (TT - 1) = -((1 - X) * (1 + Y)) := by
  have hL : (1 - X) * (TT - 1) = X * Y - Y - (1 - X) := by
    rw [← X_mul_Y, mul_sub, mul_one, ← mul_assoc, sub_mul, one_mul, X_mul_X, sub_mul, one_mul]
  have hR : (1 - X) * (1 + Y) = (1 - X) + (Y - X * Y) := by
    rw [mul_add, mul_one, sub_mul, one_mul]
  rw [hL, hR]
  abel

theorem IM_one_sub_X_mul_one_add_X : (1 - X) * (X + 1) = 0 := by
  rw [mul_add, mul_one, sub_mul, one_mul, X_mul_X]
  abel

theorem IM_ipDirect_of_torsion
    (h : ∀ u : RR, (1 - X) * (1 + Y) * (TT - 1) * u = 0 → u = 0) :
    ∀ {u w : RR}, (TT - 1) ^ 2 * u = (X + 1) * w → u = 0 := by
  intro u w huw
  refine h u ?_
  have key : (1 - X) * (1 + Y) = -((1 - X) * (TT - 1)) := by
    rw [IM_one_sub_X_mul_TT_sub_one, neg_neg]
  have hmain : (1 - X) * (1 + Y) * (TT - 1) * u = -((1 - X) * ((TT - 1) ^ 2 * u)) := by
    rw [key, neg_mul, sq]
    noncomm_ring
  rw [hmain, huw, ← mul_assoc, IM_one_sub_X_mul_one_add_X, zero_mul, neg_zero]


/-! ## The directness in `R = ℂ[SL(2,ℤ)]` modulo the collapse ideal -/

theorem idealI_direct_augIdeal {A B : Work.Kernels.R}
    (h : (Work.Kernels.R_T - 1) ^ 2 * A + Work.Kernels.R_S * (Work.Kernels.R_T - 1) ^ 2 * B ∈ Work.Residues.augIdeal) :
    A ∈ Work.Residues.augIdeal ∧ B ∈ Work.Residues.augIdeal := by
  have hΓ : (Work.Modular.tR - 1) ^ 2 * Xi A + Work.Modular.sR * (Work.Modular.tR - 1) ^ 2 * Xi B
      = 0 := by
    have h0 : Xi ((R_T - 1) ^ 2 * A + R_S * (R_T - 1) ^ 2 * B) = 0 := Xi_eq_zero_of_mem h
    have hR : Xi ((R_T - 1) ^ 2 * A) = (Work.Modular.tR - 1) ^ 2 * Xi A := by
      rw [map_mul, map_pow, map_sub, Xi_R_T, map_one]
    have hS : Xi (R_S * (R_T - 1) ^ 2 * B)
        = Work.Modular.sR * (Work.Modular.tR - 1) ^ 2 * Xi B := by
      rw [map_mul, map_mul, map_pow, map_sub, Xi_R_T, Xi_R_S, map_one]
    rw [map_add, hR, hS] at h0
    exact h0
  obtain ⟨hA, hB⟩ :=
    groupRing_direct_of_FP (fp_direct_of_halves IM_idealImDirect
      (fun {u w : RR} (hw : (TT - 1) ^ 2 * u = (X + 1) * w) =>
        Work.FreeProduct.IdealIpDirect hw)) hΓ
  exact ⟨mem_augIdeal_of_Xi_eq_zero hA, mem_augIdeal_of_Xi_eq_zero hB⟩

end Work.Residues
