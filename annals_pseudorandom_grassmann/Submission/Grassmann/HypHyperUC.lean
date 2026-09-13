import Submission.Grassmann.HypInductiveStep
import Submission.Grassmann.Hypercontractivity
import Submission.Grassmann.HypBSglob
import Submission.Commons.LinearAlgebra.Submodule.exists_linearMap_ker_range
import Submission.Commons.LinearAlgebra.Submodule.mul_mul_bijOn_hom_subtype

/-!
# Theorem 1.5 of arXiv:2209.04243 and its consequence `HypHyper`

The last remaining deep input of route (B) is the paper's Theorem 1.5
(`thm:Hypercontractivity in the Bilinear scheme`): for `f` of degree at most `d`,

  `‖f‖₄⁴ ≤ q^{100d²} Σ_{V₁ ≤ V, W₁ ≤ W} E_T ‖D_{V₁,W₁,T}[f]‖₂⁴`,

where `D_{V₁,W₁,T}[f] = (L_{V₁,W₁}[f])_{(V₁,W₁)→T}` is the (hybrid) derivative of order
`dim V₁ + codim W₁`.

This file

* defines the intrinsic averaged fourth power `D4 V₁ W₁ f` of the derivative
  (`E_T (‖D_{V₁,W₁,T}[f]‖₂²)²`, expressed through the subtype `Hom(V/V₁, W₁)` of linear maps
  killed by `V₁` with image in `W₁`, so that **no choice of a quotient map `Q` or of an
  inclusion `ι` is needed**);
* proves `l2sq_restr_shift_eq_homSub`: for any realisation `(Q, ι)` of the pair,
  `‖g_{(V₁,W₁)→T}‖₂²` is the average of `‖g‖²` over the coset `T + Hom(V/V₁, W₁)`
  (this is the well-definedness of `D4`);
* proves `D4_le`: under `SmallInfl d ε f` (i.e. pointwise `‖D_{V₁,W₁,T}[f]‖₂² ≤ ε`),
  `D4 V₁ W₁ (L_{V₁,W₁}f) ≤ ε ‖L_{V₁,W₁}f‖₂²` (small influences + the shift average
  `sum_l2sq_restr_shift`);
* packages Theorem 1.5 as the `Prop` `HypHyperUC` and derives the project's `HypHyper`
  from it.

The chain `HypHyperUC ⟹ HypHyper ⟹ {HypCor4, HypSSE, HypBSglob}` is now complete, so
`HypHyperUC` (= Theorem 1.5) is the single remaining hypothesis of route (B) besides the
BKS reduction.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-- The set of linear maps `V/V₁ → W₁`, encoded as matrices killed by `V₁` with image in `W₁`. -/
abbrev homSub {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) : Type :=
  {B : Matrix (Fin m) (Fin n) 𝔽₂ //
    V₁ ≤ LinearMap.ker B.mulVecLin ∧ LinearMap.range B.mulVecLin ≤ W₁}

/-- `E_T (‖D_{V₁,W₁,T}[f]‖₂²)²`, expressed without choosing a parametrisation of `V/V₁`
and of `W₁`. -/
def D4 {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℝ :=
  ((2 : ℝ) ^ (m * n))⁻¹ * ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
    (((Nat.card (homSub V₁ W₁) : ℝ))⁻¹ * ∑ B : homSub V₁ W₁, ‖f (B.1 + T)‖ ^ 2) ^ 2

/-- **The squared norm of a restricted, shifted function is intrinsic**: for any realisation
`(Q, ι)` of the pair `(V₁, W₁)` (with `ker Q = V₁`, `Q` onto, `range ι = W₁`, `ι` injective),
`‖g_{(V₁,W₁)→T}‖₂²` is the average of `‖g‖²` over the coset `T + Hom(V/V₁, W₁)`. -/
theorem l2sq_restr_shift_eq_homSub {m n m' n' : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (hQ : LinearMap.ker Q.mulVecLin = V₁) (hQr : LinearMap.range Q.mulVecLin = ⊤)
    (hι : LinearMap.range ι.mulVecLin = W₁) (hιk : LinearMap.ker ι.mulVecLin = ⊥)
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (restr Q ι (shift T g)) =
      ((Nat.card (homSub V₁ W₁) : ℝ))⁻¹ * ∑ B : homSub V₁ W₁, ‖g (B.1 + T)‖ ^ 2 := by
  have hbij := Commons.LinearAlgebra.Submodule.mul_mul_bijOn_hom_subtype V₁ W₁ Q ι hQ hQr hι hιk
  let fwd : Matrix (Fin m') (Fin n') 𝔽₂ → homSub V₁ W₁ :=
    fun A => ⟨ι * A * Q, hbij.mapsTo (Set.mem_univ A)⟩
  have hfwd_inj : Function.Injective fwd := by
    intro A A' h
    exact hbij.injOn (Set.mem_univ A) (Set.mem_univ A') (Subtype.ext_iff.mp h)
  have hfwd_surj : Function.Surjective fwd := by
    intro B
    obtain ⟨A, -, hA⟩ := hbij.surjOn B.2
    exact ⟨A, Subtype.ext hA⟩
  have hcard_eq : Nat.card (homSub V₁ W₁) = Nat.card (Matrix (Fin m') (Fin n') 𝔽₂) :=
    (Nat.card_congr (Equiv.ofBijective fwd ⟨hfwd_inj, hfwd_surj⟩)).symm
  have hcard' : Nat.card (homSub V₁ W₁) = 2 ^ (m' * n') := by
    rw [hcard_eq, natCard_matrix_zmod_two]
  have hsum : (∑ A : Matrix (Fin m') (Fin n') 𝔽₂, ‖g (ι * A * Q + T)‖ ^ 2) =
      ∑ B : homSub V₁ W₁, ‖g (B.1 + T)‖ ^ 2 := by
    refine Finset.sum_bij (fun A _ => fwd A) (fun A _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro A _ A' _ h
      exact hfwd_inj h
    · intro B _
      obtain ⟨A, hA⟩ := hfwd_surj B
      exact ⟨A, Finset.mem_univ _, hA⟩
    · intro A _
      rfl
  have hstep : ∀ A : Matrix (Fin m') (Fin n') 𝔽₂,
      ‖restr Q ι (shift T g) A‖ ^ 2 = ‖g (ι * A * Q + T)‖ ^ 2 := fun A => by
    rw [restr_shift_apply]
  rw [l2sq, Finset.sum_congr rfl (fun A _ => hstep A), hsum, hcard']
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- **The fourth power of a restricted, shifted function is intrinsic** (the `‖·‖₄⁴` analogue of
`l2sq_restr_shift_eq_homSub`). -/
theorem l4q_restr_shift_eq_homSub {m n m' n' : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (hQ : LinearMap.ker Q.mulVecLin = V₁) (hQr : LinearMap.range Q.mulVecLin = ⊤)
    (hι : LinearMap.range ι.mulVecLin = W₁) (hιk : LinearMap.ker ι.mulVecLin = ⊥)
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l4q (restr Q ι (shift T g)) =
      ((Nat.card (homSub V₁ W₁) : ℝ))⁻¹ * ∑ B : homSub V₁ W₁, ‖g (B.1 + T)‖ ^ 4 := by
  have hbij := Commons.LinearAlgebra.Submodule.mul_mul_bijOn_hom_subtype V₁ W₁ Q ι hQ hQr hι hιk
  let fwd : Matrix (Fin m') (Fin n') 𝔽₂ → homSub V₁ W₁ :=
    fun A => ⟨ι * A * Q, hbij.mapsTo (Set.mem_univ A)⟩
  have hfwd_inj : Function.Injective fwd := by
    intro A A' h
    exact hbij.injOn (Set.mem_univ A) (Set.mem_univ A') (Subtype.ext_iff.mp h)
  have hfwd_surj : Function.Surjective fwd := by
    intro B
    obtain ⟨A, -, hA⟩ := hbij.surjOn B.2
    exact ⟨A, Subtype.ext hA⟩
  have hcard_eq : Nat.card (homSub V₁ W₁) = Nat.card (Matrix (Fin m') (Fin n') 𝔽₂) :=
    (Nat.card_congr (Equiv.ofBijective fwd ⟨hfwd_inj, hfwd_surj⟩)).symm
  have hcard' : Nat.card (homSub V₁ W₁) = 2 ^ (m' * n') := by
    rw [hcard_eq, natCard_matrix_zmod_two]
  have hsum : (∑ A : Matrix (Fin m') (Fin n') 𝔽₂, ‖g (ι * A * Q + T)‖ ^ 4) =
      ∑ B : homSub V₁ W₁, ‖g (B.1 + T)‖ ^ 4 := by
    refine Finset.sum_bij (fun A _ => fwd A) (fun A _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro A _ A' _ h
      exact hfwd_inj h
    · intro B _
      obtain ⟨A, hA⟩ := hfwd_surj B
      exact ⟨A, Finset.mem_univ _, hA⟩
    · intro A _
      rfl
  have hstep : ∀ A : Matrix (Fin m') (Fin n') 𝔽₂,
      ‖restr Q ι (shift T g) A‖ ^ 4 = ‖g (ι * A * Q + T)‖ ^ 4 := fun A => by
    rw [restr_shift_apply]
  rw [l4q, Finset.sum_congr rfl (fun A _ => hstep A), hsum, hcard']
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- **The averaging identity for restrictions and fourth powers**: averaging the normalised
fourth power of the restriction of `g` over the shift `T` recovers the normalised fourth power
of `g`, for any pair `(V₁, W₁)`.

This is the "bound the 4-norm of each restriction and take the expectation over a random `T`"
step of arXiv:2209.04243 §8. -/
theorem l4q_eq_avg_restr {m n m' n' : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (hQ : LinearMap.ker Q.mulVecLin = V₁) (hQr : LinearMap.range Q.mulVecLin = ⊤)
    (hι : LinearMap.range ι.mulVecLin = W₁) (hιk : LinearMap.ker ι.mulVecLin = ⊥)
    (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l4q g = ((2 : ℝ) ^ (m * n))⁻¹ *
      ∑ T : Matrix (Fin m) (Fin n) 𝔽₂, l4q (restr Q ι (shift T g)) := by
  haveI : Nonempty (homSub V₁ W₁) :=
    ⟨⟨0, by simp [LinearMap.ker_eq_top, LinearMap.range_eq_bot]⟩⟩
  set c : ℝ := ((Nat.card (homSub V₁ W₁) : ℝ))⁻¹ with hc
  have hpt : ∀ T : Matrix (Fin m) (Fin n) 𝔽₂,
      l4q (restr Q ι (shift T g)) = c * ∑ B : homSub V₁ W₁, ‖g (B.1 + T)‖ ^ 4 :=
    fun T => l4q_restr_shift_eq_homSub V₁ W₁ Q ι hQ hQr hι hιk T g
  have hshift : ∀ B : homSub V₁ W₁,
      (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, ‖g (B.1 + T)‖ ^ 4) =
        ∑ T : Matrix (Fin m) (Fin n) 𝔽₂, ‖g T‖ ^ 4 := by
    intro B
    refine Fintype.sum_equiv (Equiv.addLeft B.1) (fun T => ‖g (B.1 + T)‖ ^ 4)
      (fun T => ‖g T‖ ^ 4) (fun T => ?_)
    simp [Equiv.addLeft]
  have htotal : (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, ‖g T‖ ^ 4) = (2 : ℝ) ^ (m * n) * l4q g := by
    rw [l4q, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0)), one_mul]
  have h2 : ∀ B : homSub V₁ W₁,
      (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, ‖g (B.1 + T)‖ ^ 4) = (2 : ℝ) ^ (m * n) * l4q g :=
    fun B => (hshift B).trans htotal
  have key : (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, ∑ B : homSub V₁ W₁, ‖g (B.1 + T)‖ ^ 4) =
      (Nat.card (homSub V₁ W₁) : ℝ) * ((2 : ℝ) ^ (m * n) * l4q g) := by
    rw [Finset.sum_comm]
    simp only [h2, Finset.sum_const, Nat.card_eq_fintype_card, Finset.card_univ, nsmul_eq_mul]
  have hH : ((Nat.card (homSub V₁ W₁) : ℝ)) ≠ 0 := by
    have hpos : 0 < Nat.card (homSub V₁ W₁) := Nat.card_pos
    exact_mod_cast ne_of_gt hpos
  rw [Finset.sum_congr rfl (fun T _ => hpt T), ← Finset.mul_sum, key]
  simp only [hc]
  field_simp

/-! ## The order cut-off: for `DegLe d f` only pairs of order `≤ d` contribute -/

/-- The order of a hybrid pair bounds the rank of every character it keeps. -/
lemma hybridPredSub_order_le_rank {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hX : hybridPredSub V₁ W₁ X) :
    Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ X.rank := by
  have hker : LinearMap.ker X.mulVecLin ≤ W₁ := fun w hw => hX.2 w (by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
    rw [hw]; exact V₁.zero_mem)
  -- `X⁻¹(V₁) = ker X ⊔ (V₁ ∩ Im X) = ker X + V₁` has dimension `finrank (ker X) + finrank V₁`
  have hcomap := Commons.LinearAlgebra.finrank_comap_eq X.mulVecLin V₁
  have hinf : V₁ ⊓ LinearMap.range X.mulVecLin = V₁ := inf_eq_left.mpr hX.1
  rw [hinf] at hcomap
  have hsub : Submodule.comap X.mulVecLin V₁ ≤ W₁ := hX.2
  have hle : Module.finrank 𝔽₂ ↥(LinearMap.ker X.mulVecLin) + Module.finrank 𝔽₂ ↥V₁
      ≤ Module.finrank 𝔽₂ ↥W₁ := by
    rw [← hcomap]
    exact Submodule.finrank_mono hsub
  have hrn := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
  rw [Module.finrank_fin_fun (R := 𝔽₂)] at hrn
  have hWle : Module.finrank 𝔽₂ ↥W₁ ≤ m := by
    have := Submodule.finrank_le (R := 𝔽₂) W₁
    rwa [Module.finrank_fin_fun (R := 𝔽₂)] at this
  have hXr : X.rank = Module.finrank 𝔽₂ (LinearMap.range X.mulVecLin) := rfl
  omega

/-- For a function of degree at most `d` the hybrid Laplacian `L_{V₁,W₁}` vanishes as soon as
its order `dim V₁ + codim W₁` exceeds `d`.  (This is the "the equality is trivial" remark after
Theorem 1.5 of arXiv:2209.04243.) -/
theorem Lsub_eq_zero_of_lt_order {m n d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (h : d < Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)) : Lsub V₁ W₁ f = 0 := by
  refine eq_of_fcoeff_eq (fun X => ?_)
  rw [Lsub, fcoeff_lapMulN, fcoeff_zero]
  by_cases hX : hybridPredSub V₁ W₁ X
  · have hle := hybridPredSub_order_le_rank V₁ W₁ X hX
    rw [if_pos hX, fcoeff_eq, hf X (by omega), mul_zero, one_mul]
  · rw [if_neg hX, zero_mul]

/-- `D4 V₁ W₁ 0 = 0`. -/
lemma D4_zero {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) :
    D4 V₁ W₁ (0 : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) = 0 := by
  unfold D4
  simp

/-- For `DegLe d f`, the sum defining `HypHyperUC` may be taken over *all* pairs `(V₁,W₁)`:
the pairs of order `> d` contribute nothing. -/
theorem sum_D4_eq_sum_D4_of_degLe {m n d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) :
    (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
          then D4 V₁ W₁ (Lsub V₁ W₁ f) else 0) =
      ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        D4 V₁ W₁ (Lsub V₁ W₁ f) := by
  refine Finset.sum_congr rfl (fun V₁ _ => Finset.sum_congr rfl (fun W₁ _ => ?_))
  by_cases hord : Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
  · rw [if_pos hord]
  · rw [if_neg hord, Lsub_eq_zero_of_lt_order hf V₁ W₁ (by omega), D4_zero]

/-- **The per-pair small-influence bound**: if `f` has `(d,ε)`-small generalised influences then
the averaged fourth power of the derivative of `L_{V₁,W₁}[f]` is at most `ε` times the squared
norm of `L_{V₁,W₁}[f]`. -/
lemma D4_le {m n d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} {ε : ℝ}
    (hSI : SmallInfl d ε f) (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (horder : Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d) :
    D4 V₁ W₁ (Lsub V₁ W₁ f) ≤ ε * l2sq (Lsub V₁ W₁ f) := by
  obtain ⟨n', Q, hQ, hQr⟩ := (Commons.LinearAlgebra.Submodule.exists_linearMap_ker_range n V₁).1
  obtain ⟨m', ι, hι, hιk⟩ := (Commons.LinearAlgebra.Submodule.exists_linearMap_ker_range m W₁).2
  have hD4 : D4 V₁ W₁ (Lsub V₁ W₁ f) =
      ((2 : ℝ) ^ (m * n))⁻¹ * ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
        (l2sq (restr Q ι (shift T (Lsub V₁ W₁ f)))) ^ 2 := by
    unfold D4
    congr 1
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [l2sq_restr_shift_eq_homSub V₁ W₁ Q ι hQ hQr hι hιk T (Lsub V₁ W₁ f)]
  rw [hD4]
  have hpt : ∀ T : Matrix (Fin m) (Fin n) 𝔽₂,
      l2sq (restr Q ι (shift T (Lsub V₁ W₁ f))) ≤ ε := by
    intro T
    have hord : hybridOrder Q ι ≤ d := by
      rw [hybridOrder, hQ, hι]; exact horder
    have hthis := hSI Q ι T hord
    have h1 : inflBS2 Q ι T f = l2sq (restr Q ι (shift T (Lsub V₁ W₁ f))) := by
      rw [inflBS2, Lsub, hybridPred_eq_hybridPredSub, hQ, hι]
    rwa [h1] at hthis
  have hpt2 : ∀ T : Matrix (Fin m) (Fin n) 𝔽₂,
      (l2sq (restr Q ι (shift T (Lsub V₁ W₁ f)))) ^ 2 ≤
        ε * l2sq (restr Q ι (shift T (Lsub V₁ W₁ f))) := by
    intro T
    have h1 := hpt T
    have h2 := l2sq_nonneg (restr Q ι (shift T (Lsub V₁ W₁ f)))
    nlinarith [h1, h2]
  calc ((2 : ℝ) ^ (m * n))⁻¹ * ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
        (l2sq (restr Q ι (shift T (Lsub V₁ W₁ f)))) ^ 2
      ≤ ((2 : ℝ) ^ (m * n))⁻¹ *
          (ε * ∑ T : Matrix (Fin m) (Fin n) 𝔽₂, l2sq (restr Q ι (shift T (Lsub V₁ W₁ f)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun T _ => hpt2 T)
    _ = ((2 : ℝ) ^ (m * n))⁻¹ *
          (ε * ((2 : ℝ) ^ (m * n) * l2sq (Lsub V₁ W₁ f))) := by
        rw [sum_l2sq_restr_shift]
    _ = ε * l2sq (Lsub V₁ W₁ f) := by
        have h2 : ((2 : ℝ) ^ (m * n)) ≠ 0 := pow_ne_zero _ (by norm_num)
        field_simp

/-- **Theorem 1.5 of arXiv:2209.04243** (`thm:Hypercontractivity in the Bilinear scheme`), in
the intrinsic form: for a function of degree at most `d`,

  `‖f‖₄⁴ ≤ q^{Cd²} Σ_{V₁ ≤ V, W₁ ≤ W : dim V₁ + codim W₁ ≤ d} E_T ‖D_{V₁,W₁,T}[f]‖₂⁴`. -/
def HypHyperUC : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (m n : ℕ) (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ), DegLe d f →
    l4q f ≤ (2 : ℝ) ^ (C * d ^ 2) *
      ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
          then D4 V₁ W₁ (Lsub V₁ W₁ f) else 0

/-- **Theorem 1.5 implies the paper's `cor:Corollary of hypercontractivity` form used
throughout the project**: combining the intrinsic hypercontractive inequality with the
pointwise small-influence bound and the shift average. -/
theorem HypHyper_of_HypHyperUC (H : HypHyperUC) : HypHyper := by
  obtain ⟨C, hC, h⟩ := H
  refine ⟨C, hC, ?_⟩
  intro m n d f ε hε hdeg hSI
  have hmain : (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
          then D4 V₁ W₁ (Lsub V₁ W₁ f) else 0) ≤ ε * pairSum d f := by
    rw [pairSum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun V₁ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun W₁ _ => ?_)
    by_cases hord : Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
    · rw [if_pos hord, if_pos hord]
      exact D4_le hSI V₁ W₁ hord
    · rw [if_neg hord, if_neg hord]
      exact mul_nonneg hε le_rfl
  have h2 := mul_le_mul_of_nonneg_left hmain
    (show (0:ℝ) ≤ (2:ℝ) ^ (C * d ^ 2) by positivity)
  refine (h m n d f hdeg).trans ?_
  exact h2.trans (le_of_eq (by ring))

/-! ## Corollaries -/

/-- The paper's `cor:Corollary of hypercontractivity` from Theorem 1.5. -/
theorem HypCor4_of_HypHyperUC (H : HypHyperUC) : HypCor4 :=
  HypCor4_of_HypHyper (HypHyper_of_HypHyperUC H)

/-- The paper's Theorem 1.6 (small-set expansion for the shortcode graph) from Theorem 1.5. -/
theorem HypSSE_of_HypHyperUC (H : HypHyperUC) : HypSSE :=
  HypSSE_of_HypHyper (HypHyper_of_HypHyperUC H)

/-- The paper's `cor:atmostd` from Theorem 1.5. -/
theorem HypBSglob_of_HypHyperUC (H : HypHyperUC) : HypBSglob :=
  HypBSglob_of_HypCor4 (HypCor4_of_HypHyperUC H)

end

end Submission.Grassmann
