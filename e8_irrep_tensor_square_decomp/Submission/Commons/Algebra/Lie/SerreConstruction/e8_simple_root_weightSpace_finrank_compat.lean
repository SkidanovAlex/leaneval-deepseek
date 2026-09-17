import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_zero_weightSpace_finrank
import Submission.Commons.Algebra.Lie.SerreConstruction.borel_side_span_top
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_serreE_ne_zero
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posDef

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000

noncomputable section
open CartanMatrix

namespace Commons.Algebra.Lie.SerreConstruction

/-!
# The weight space of the Serre-constructed `e₈` at a simple root (compatibility version)

This is a compatibility re-proof of `e8_simple_root_weightSpace_finrank`.  It imports
`Submission.Commons.Algebra.Lie.SerreConstruction.e8_zero_weightSpace_finrank` (which already
provides `L8`, `SerreH`, `SerreE`, `SerreF`, `W`, `mem_W_iff`, the star model, the Cartan
generators and their Serre relations) and reuses those definitions instead of redefining them, so
that it can be imported together with `e8_weightSpace_reflect_finrank`.

The claim is: the joint weight space of the Serre-constructed `e₈(ℂ)` at the simple root `α_k`
(whose coordinates are the `k`-th row of the Cartan matrix, `α_k i = A k i`) is one-dimensional.

The proof is the same as the original: a triangular decomposition
`L8 = ĥ ⊔ n⁺ ⊔ n⁻` (from `borel_side_span_top` pushed along the quotient map), weight-space
decompositions of `n⁺` and `n⁻`, the "killer operator" separation of weight vectors, and the
non-vanishing `eₖ ≠ 0` (`e8_serreE_ne_zero`).
-/

/-- The quotient Lie algebra morphism `FL8 → L8`. -/
noncomputable def quotHom : FL8 →ₗ⁅ℂ⁆ L8 :=
  { toLinearMap := (LieSubmodule.Quotient.mk' (CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)).toLinearMap
    map_lie' := fun {x y} => LieSubmodule.Quotient.mk_bracket _ x y }

lemma quotHom_apply (x : FL8) :
    quotHom x = LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈) x :=
  rfl

lemma quotHom_surjective : Function.Surjective quotHom :=
  LieSubmodule.Quotient.surjective_mk' _

lemma quotHom_of_H (i : Fin 8) : quotHom (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i)) = SerreH i := rfl
lemma quotHom_of_E (i : Fin 8) : quotHom (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i)) = SerreE i := rfl
lemma quotHom_of_F (i : Fin 8) : quotHom (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)) = SerreF i := rfl


private lemma quotHom_eq_zero_of_toSet {x : FL8}
    (hx : x ∈ CartanMatrix.Relations.toSet ℂ CartanMatrix.E₈) : quotHom x = 0 := by
  rw [quotHom_apply, LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan hx


/-! ## Weight spaces of the adjoint action of the Cartan generators -/

/-- The `k`-th simple root, as a functional on the Cartan generators: `α_k i = A k i` (the `k`-th
row of the Cartan matrix). -/
def alpha (k : Fin 8) : Fin 8 → ℂ := fun i => ((CartanMatrix.E₈ k i : ℤ) : ℂ)

lemma W_neg_mem {μ : Fin 8 → ℂ} {x : L8} (hx : x ∈ W μ) : -x ∈ W μ := (W μ).neg_mem hx
lemma W_add_mem {μ : Fin 8 → ℂ} {x y : L8} (hx : x ∈ W μ) (hy : y ∈ W μ) : x + y ∈ W μ :=
  (W μ).add_mem hx hy
lemma W_smul_mem {μ : Fin 8 → ℂ} (c : ℂ) {x : L8} (hx : x ∈ W μ) : c • x ∈ W μ :=
  (W μ).smul_mem c hx

/-- The `E`-generator `eⱼ` lies in the weight space of the simple root `αⱼ`. -/
lemma SerreE_mem_W (j : Fin 8) : SerreE j ∈ W (alpha j) := by
  rw [mem_W_iff]
  intro i
  rw [serreLie_H_E, alpha]
  rw [← Int.cast_smul_eq_zsmul ℂ (CartanMatrix.E₈ i j) (SerreE j),
    show CartanMatrix.E₈ i j = CartanMatrix.E₈ j i from E8_symm i j]

/-- The `F`-generator `fⱼ` lies in the weight space of the weight `-αⱼ`. -/
lemma SerreF_mem_W (j : Fin 8) : SerreF j ∈ W (-(alpha j)) := by
  rw [mem_W_iff]
  intro i
  rw [serreLie_H_F]
  rw [show (-(CartanMatrix.E₈ i j)) • SerreF j
      = ((-(CartanMatrix.E₈ i j) : ℤ) : ℂ) • SerreF j from
        (Int.cast_smul_eq_zsmul ℂ (-(CartanMatrix.E₈ i j)) (SerreF j)).symm]
  congr 1
  rw [Pi.neg_apply, alpha, show CartanMatrix.E₈ i j = CartanMatrix.E₈ j i from E8_symm i j,
    Int.cast_neg]

/-- An element of `W μ` is killed by the operator `ad (H i) - μ i`. -/
lemma killer_apply_eq_zero {μ : Fin 8 → ℂ} {x : L8} (hx : x ∈ W μ) (i : Fin 8) :
    (LieAlgebra.ad ℂ L8 (SerreH i) - μ i • 1) x = 0 := by
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, LieAlgebra.ad_apply,
    (mem_W_iff.mp hx i), sub_self]

/-! ## The weight lattice: `∑ᵢ mᵢ αᵢ` and its injectivity -/

/-- The rational weight vector `∑ᵢ mᵢ αᵢ` (in `ω`-coordinates), for an integer vector `m`. -/
def QWtSum (m : Fin 8 → ℤ) : Fin 8 → ℚ :=
  fun j => ∑ i, (m i : ℚ) * (CartanMatrix.E₈ i j : ℚ)

/-- The complex weight vector `∑ᵢ mᵢ αᵢ`, the weight functional of the vector `∑ᵢ mᵢ eᵢ`. -/
def WtSum (m : Fin 8 → ℤ) : Fin 8 → ℂ :=
  fun j => ∑ i, ((m i : ℤ) : ℂ) * alpha i j

lemma QWtSum_eq_cast (m : Fin 8 → ℤ) (j : Fin 8) :
    ((QWtSum m j : ℚ) : ℂ) = WtSum m j := by
  simp only [QWtSum, WtSum, alpha, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]

/-- **The rows of the `E₈` Cartan matrix are linearly independent over `ℚ`** (equivalently, the
weight map `m ↦ ∑ᵢ mᵢ αᵢ` is injective): immediate from positive definiteness of `E₈`. -/
lemma QWtSum_injective : Function.Injective QWtSum := by
  intro m m' h
  by_contra hne
  set v : Fin 8 → ℚ := fun i => ((m i - m' i : ℤ) : ℚ) with hvdef
  have hv : v ≠ 0 := by
    intro h0
    apply hne
    funext i
    have h1 := congrFun h0 i
    simp only [Pi.zero_apply, hvdef] at h1
    have hz : (m i - m' i : ℤ) = 0 := by exact_mod_cast h1
    exact sub_eq_zero.mp hz
  have hd : ∀ j : Fin 8, (∑ i, v i * (CartanMatrix.E₈ i j : ℚ)) = 0 := by
    intro j
    have hj := congrFun h j
    simp only [QWtSum] at hj
    have h2 : (∑ i, (m i : ℚ) * (CartanMatrix.E₈ i j : ℚ))
        - (∑ i, (m' i : ℚ) * (CartanMatrix.E₈ i j : ℚ)) = 0 := sub_eq_zero.mpr hj
    rw [← Finset.sum_sub_distrib] at h2
    rwa [show (∑ i, ((m i : ℚ) * (CartanMatrix.E₈ i j : ℚ)
        - (m' i : ℚ) * (CartanMatrix.E₈ i j : ℚ)))
        = ∑ i, v i * (CartanMatrix.E₈ i j : ℚ) from by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hvdef]
      push_cast
      ring] at h2
  have hzero : (∑ i, ∑ j, v i * (CartanMatrix.E₈ i j : ℚ) * v j) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : (∑ i, v i * (CartanMatrix.E₈ i j : ℚ) * v j)
        = (∑ i, v i * (CartanMatrix.E₈ i j : ℚ)) * v j :=
      (Finset.sum_mul Finset.univ (fun i => v i * (CartanMatrix.E₈ i j : ℚ)) (v j)).symm
    rw [this, hd j, zero_mul]
  have hpos := Commons.LinearAlgebra.Matrix.Cartan.E8_posDef v hv
  linarith

/-- The weight map `m ↦ ∑ᵢ mᵢ αᵢ` is injective. -/
lemma WtSum_injective : Function.Injective WtSum := by
  intro m m' h
  apply QWtSum_injective
  funext j
  have h1 : ((QWtSum m j : ℚ) : ℂ) = ((QWtSum m' j : ℚ) : ℂ) := by
    rw [QWtSum_eq_cast, QWtSum_eq_cast, congrFun h j]
  exact Rat.cast_injective h1

@[simp] lemma WtSum_zero : WtSum 0 = 0 := by
  funext j; simp [WtSum]

lemma WtSum_add (m m' : Fin 8 → ℤ) : WtSum (m + m') = WtSum m + WtSum m' := by
  funext j
  simp only [WtSum, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

lemma WtSum_neg (m : Fin 8 → ℤ) : WtSum (-m) = -WtSum m := by
  funext j
  simp only [WtSum, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

lemma WtSum_single (k : Fin 8) : WtSum (Pi.single k 1) = alpha k := by
  funext j
  simp only [WtSum, alpha, Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ k (fun i => ((CartanMatrix.E₈ i j : ℤ) : ℂ))]
  simp

/-- The nonnegative weights `∑ᵢ mᵢ αᵢ`, `m ≥ 0`. -/
def NWtSum (m : Fin 8 → ℕ) : Fin 8 → ℂ := WtSum (fun i => (m i : ℤ))

@[simp] lemma NWtSum_zero : NWtSum 0 = 0 := by
  simp only [NWtSum, Pi.zero_apply]
  exact WtSum_zero

lemma NWtSum_add (m m' : Fin 8 → ℕ) : NWtSum (m + m') = NWtSum m + NWtSum m' := by
  funext j
  simp only [NWtSum, WtSum, Pi.add_apply, Nat.cast_add, Int.cast_add, add_mul,
    Finset.sum_add_distrib]

lemma NWtSum_single (k : Fin 8) : NWtSum (Pi.single k (1 : ℕ)) = alpha k := by
  have h : (fun i => (((Pi.single k (1 : ℕ) : Fin 8 → ℕ) i : ℕ) : ℤ)) = Pi.single k (1 : ℤ) := by
    funext i
    by_cases hik : i = k
    · subst hik; simp
    · rw [Pi.single_eq_of_ne (M := fun _ => ℕ) hik,
        Pi.single_eq_of_ne' (M := fun _ => ℤ) (Ne.symm hik)]
      simp
  simp only [NWtSum, h, WtSum_single]

/-- `∑ᵢ mᵢαᵢ = 0` with all `mᵢ ≥ 0` forces `m = 0`. -/
lemma NWtSum_eq_zero {m : Fin 8 → ℕ} (h : NWtSum m = 0) : m = 0 := by
  have h' : (fun i => (m i : ℤ)) = 0 := by
    apply WtSum_injective
    rw [show WtSum (fun i => (m i : ℤ)) = NWtSum m from rfl, h]
    exact WtSum_zero.symm
  funext i
  have h3 : (m i : ℤ) = 0 := by
    have := congrFun h' i
    simpa only [Pi.zero_apply] using this
  change m i = 0
  omega

/-- `∑ᵢ mᵢαᵢ = α_k` with `m ≥ 0` forces `m = e_k`. -/
lemma NWtSum_eq_alpha {m : Fin 8 → ℕ} {k : Fin 8} (h : NWtSum m = alpha k) :
    m = Pi.single k 1 := by
  have h' : (fun i => (m i : ℤ)) = Pi.single k (1 : ℤ) := by
    apply WtSum_injective
    rw [show WtSum (fun i => (m i : ℤ)) = NWtSum m from rfl, h, WtSum_single]
  funext i
  have hi := congrFun h' i
  simp only [Pi.single_apply] at hi
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl] at hi
    rw [Pi.single_eq_same]
    omega
  · rw [if_neg hik] at hi
    rw [Pi.single_eq_of_ne' (M := fun _ => ℕ) (Ne.symm hik)]
    omega

/-- `∑ᵢ mᵢαᵢ ≠ α_k` unless `m = e_k`. -/
lemma NWtSum_ne_alpha {m : Fin 8 → ℕ} {k : Fin 8} (hm : m ≠ Pi.single k 1) :
    NWtSum m ≠ alpha k :=
  fun h => hm (NWtSum_eq_alpha h)

/-- `-∑ᵢ mᵢαᵢ ≠ α_k` for every nonnegative `m`. -/
lemma neg_NWtSum_ne_alpha (m : Fin 8 → ℕ) (k : Fin 8) : -NWtSum m ≠ alpha k := by
  intro h
  have h1 : WtSum (fun i => (m i : ℤ)) + WtSum (Pi.single k 1) = 0 := by
    rw [show WtSum (fun i => (m i : ℤ)) = NWtSum m from rfl, WtSum_single, ← h]
    abel
  rw [← WtSum_add] at h1
  have h2 : (fun i => (m i : ℤ)) + Pi.single k 1 = 0 := WtSum_injective (by rw [h1]; exact WtSum_zero.symm)
  have hk := congrFun h2 k
  simp only [Pi.add_apply, Pi.zero_apply, Pi.single_eq_same] at hk
  omega

/-! ## The three subalgebras, the spanning statement, and the weight pieces of `n⁺`, `n⁻` -/

/-- The span of the images of the `H`-generators. -/
abbrev Hsub : LieSubalgebra ℂ L8 := LieSubalgebra.lieSpan ℂ L8 (Set.range SerreH)

/-- The subalgebra generated by the images of the `E`-generators. -/
abbrev Psub : LieSubalgebra ℂ L8 := LieSubalgebra.lieSpan ℂ L8 (Set.range SerreE)

/-- The subalgebra generated by the images of the `F`-generators. -/
abbrev Msub : LieSubalgebra ℂ L8 := LieSubalgebra.lieSpan ℂ L8 (Set.range SerreF)

lemma W_zero_lie_mem {x y : L8} (hx : x ∈ W 0) (hy : y ∈ W 0) : ⁅x, y⁆ ∈ W 0 := by
  have := bracket_mem_W hx hy
  rwa [zero_add] at this

/-- `W 0` viewed as a Lie subalgebra. -/
noncomputable def W0lie : LieSubalgebra ℂ L8 := { W 0 with lie_mem' := W_zero_lie_mem }

lemma Hsub_le_W_zero : (Hsub : Submodule ℂ L8) ≤ W 0 := by
  have h : Hsub ≤ W0lie :=
    LieSubalgebra.lieSpan_le.mpr (fun x hx => by obtain ⟨i, rfl⟩ := hx; exact SerreH_mem_W_zero i)
  exact fun x hx => h hx

/-- The five families of Serre relations used by `borel_side_span_top` (all except the `ad F` ones). -/
abbrev Rel5 : Set FL8 :=
  ((Set.range (CartanMatrix.Relations.HH ℂ)) ∪ (Set.range (CartanMatrix.Relations.EF ℂ))
      ∪ (Set.range (CartanMatrix.Relations.HE ℂ CartanMatrix.E₈)))
    ∪ (Set.range (CartanMatrix.Relations.HF ℂ CartanMatrix.E₈))
    ∪ (Set.range (CartanMatrix.Relations.adE ℂ CartanMatrix.E₈))

lemma Rel5_subset_toSet : Rel5 ⊆ CartanMatrix.Relations.toSet ℂ CartanMatrix.E₈ := by
  intro x hx
  rcases hx with ((((h1 | h2) | h3) | h4) | h5)
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h2))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr h3)))
  · exact Or.inl (Or.inl (Or.inr h4))
  · exact Or.inl (Or.inr h5)

/-- **Spanning.**  The Serre-constructed `e₈` is the sum of the span of the Cartan generators, the
subalgebra generated by the `E`-generators and the subalgebra generated by the `F`-generators. -/
theorem span_H_P_M_top :
    (Hsub : Submodule ℂ L8) ⊔ (Psub : Submodule ℂ L8) ⊔ (Msub : Submodule ℂ L8) = ⊤ := by
  have h := borel_side_span_top ℂ (Fin 8) CartanMatrix.E₈
  have hsetH : quotHom '' (Set.range (fun i => FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i)))
      = Set.range SerreH := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, rfl⟩
  have hH : Submodule.map quotHom.toLinearMap
      ((LieSubalgebra.lieSpan ℂ FL8
        (Set.range (fun i => FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i)))) :
          Submodule ℂ FL8) = (Hsub : Submodule ℂ L8) := by
    have h1 : Submodule.map quotHom.toLinearMap
        ((LieSubalgebra.lieSpan ℂ FL8
          (Set.range (fun i => FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i)))) :
            Submodule ℂ FL8)
        = ((LieSubalgebra.lieSpan ℂ FL8
          (Set.range (fun i => FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i)))).map quotHom :
            Submodule ℂ L8) := rfl
    rw [h1, LieSubalgebra.map_lieSpan, hsetH]
  have hsetE : quotHom '' (Set.range (fun i => FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i)))
      = Set.range SerreE := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, rfl⟩
  have hE : Submodule.map quotHom.toLinearMap
      ((LieSubalgebra.lieSpan ℂ FL8
        (Set.range (fun i => FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i)))) :
          Submodule ℂ FL8) = (Psub : Submodule ℂ L8) := by
    have h1 : Submodule.map quotHom.toLinearMap
        ((LieSubalgebra.lieSpan ℂ FL8
          (Set.range (fun i => FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i)))) :
            Submodule ℂ FL8)
        = ((LieSubalgebra.lieSpan ℂ FL8
          (Set.range (fun i => FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i)))).map quotHom :
            Submodule ℂ L8) := rfl
    rw [h1, LieSubalgebra.map_lieSpan, hsetE]
  have hsetF : quotHom '' (Set.range (fun i => FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)))
      = Set.range SerreF := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, rfl⟩
  have hF : Submodule.map quotHom.toLinearMap
      ((LieSubalgebra.lieSpan ℂ FL8
        (Set.range (fun i => FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)))) :
          Submodule ℂ FL8) = (Msub : Submodule ℂ L8) := by
    have h1 : Submodule.map quotHom.toLinearMap
        ((LieSubalgebra.lieSpan ℂ FL8
          (Set.range (fun i => FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)))) :
            Submodule ℂ FL8)
        = ((LieSubalgebra.lieSpan ℂ FL8
          (Set.range (fun i => FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)))).map quotHom :
            Submodule ℂ L8) := rfl
    rw [h1, LieSubalgebra.map_lieSpan, hsetF]
  have hIle : LieSubmodule.lieSpan ℂ FL8 Rel5 ≤ (quotHom.ker : LieIdeal ℂ FL8) :=
    LieSubmodule.lieSpan_le.mpr (fun x hx =>
      quotHom_eq_zero_of_toSet (Rel5_subset_toSet hx))
  have hI : Submodule.map quotHom.toLinearMap
      ((LieIdeal.toLieSubalgebra ℂ FL8 (LieSubmodule.lieSpan ℂ FL8 Rel5)).toSubmodule) = ⊥ := by
    rw [← le_bot_iff, Submodule.map_le_iff_le_comap]
    intro x hx
    have := hIle hx
    simpa using this
  have htop : Submodule.map quotHom.toLinearMap (⊤ : Submodule ℂ FL8) = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr quotHom_surjective]
  rw [← htop, ← h, Submodule.map_sup, Submodule.map_sup, Submodule.map_sup, hH, hE, hF, hI,
    sup_bot_eq]

/-- The weight-`∑ mᵢαᵢ` piece of the `E`-subalgebra. -/
def Pm (m : Fin 8 → ℕ) : Submodule ℂ L8 := (Psub : Submodule ℂ L8) ⊓ W (NWtSum m)

/-- The weight-`-∑ mᵢαᵢ` piece of the `F`-subalgebra. -/
def Mm (m : Fin 8 → ℕ) : Submodule ℂ L8 := (Msub : Submodule ℂ L8) ⊓ W (-(NWtSum m))

lemma bracket_mem_Pm {m m' : Fin 8 → ℕ} {x y : L8} (hx : x ∈ Pm m) (hy : y ∈ Pm m') :
    ⁅x, y⁆ ∈ Pm (m + m') := by
  refine ⟨Psub.lie_mem hx.1 hy.1, ?_⟩
  rw [NWtSum_add]
  exact bracket_mem_W hx.2 hy.2

lemma bracket_mem_Mm {m m' : Fin 8 → ℕ} {x y : L8} (hx : x ∈ Mm m) (hy : y ∈ Mm m') :
    ⁅x, y⁆ ∈ Mm (m + m') := by
  refine ⟨Msub.lie_mem hx.1 hy.1, ?_⟩
  rw [NWtSum_add, neg_add]
  exact bracket_mem_W hx.2 hy.2

lemma SerreE_mem_Pm (i : Fin 8) : SerreE i ∈ Pm (Pi.single i 1) :=
  ⟨LieSubalgebra.subset_lieSpan (Set.mem_range_self i), by
    rw [NWtSum_single]; exact SerreE_mem_W i⟩

lemma SerreF_mem_Mm (i : Fin 8) : SerreF i ∈ Mm (Pi.single i 1) :=
  ⟨LieSubalgebra.subset_lieSpan (Set.mem_range_self i), by
    rw [NWtSum_single]; exact SerreF_mem_W i⟩

/-- The supremum of the nonnegative weight pieces of `n⁺` is closed under the Lie bracket. -/
lemma iSup_Pm_lie_mem ⦃x y : L8⦄ (hx : x ∈ ⨆ m : Fin 8 → ℕ, Pm m)
    (hy : y ∈ ⨆ m : Fin 8 → ℕ, Pm m) : ⁅x, y⁆ ∈ ⨆ m : Fin 8 → ℕ, Pm m := by
  refine Submodule.iSup_induction Pm
    (motive := fun x => ∀ y, y ∈ ⨆ m : Fin 8 → ℕ, Pm m → ⁅x, y⁆ ∈ ⨆ m, Pm m) hx ?_ ?_ ?_ y hy
  · intro m x hx y hy
    refine Submodule.iSup_induction Pm (motive := fun y => ⁅x, y⁆ ∈ ⨆ m, Pm m) hy ?_ ?_ ?_
    · intro m' y hy
      exact Submodule.mem_iSup_of_mem (m + m') (bracket_mem_Pm hx hy)
    · rw [lie_zero]; exact Submodule.zero_mem _
    · intro a b ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
  · intro y hy; rw [zero_lie]; exact Submodule.zero_mem _
  · intro a b ha hb y hy; rw [add_lie]; exact Submodule.add_mem _ (ha y hy) (hb y hy)

/-- The supremum of the nonpositive weight pieces of `n⁻` is closed under the Lie bracket. -/
lemma iSup_Mm_lie_mem ⦃x y : L8⦄ (hx : x ∈ ⨆ m : Fin 8 → ℕ, Mm m)
    (hy : y ∈ ⨆ m : Fin 8 → ℕ, Mm m) : ⁅x, y⁆ ∈ ⨆ m : Fin 8 → ℕ, Mm m := by
  refine Submodule.iSup_induction Mm
    (motive := fun x => ∀ y, y ∈ ⨆ m : Fin 8 → ℕ, Mm m → ⁅x, y⁆ ∈ ⨆ m, Mm m) hx ?_ ?_ ?_ y hy
  · intro m x hx y hy
    refine Submodule.iSup_induction Mm (motive := fun y => ⁅x, y⁆ ∈ ⨆ m, Mm m) hy ?_ ?_ ?_
    · intro m' y hy
      exact Submodule.mem_iSup_of_mem (m + m') (bracket_mem_Mm hx hy)
    · rw [lie_zero]; exact Submodule.zero_mem _
    · intro a b ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
  · intro y hy; rw [zero_lie]; exact Submodule.zero_mem _
  · intro a b ha hb y hy; rw [add_lie]; exact Submodule.add_mem _ (ha y hy) (hb y hy)

/-- **`n⁺` is the sum of its nonnegative weight pieces.** -/
lemma Psub_le_iSup_Pm : (Psub : Submodule ℂ L8) ≤ ⨆ m : Fin 8 → ℕ, Pm m := by
  let Z' : LieSubalgebra ℂ L8 :=
    LieSubalgebra.mk (⨆ m : Fin 8 → ℕ, Pm m) (fun {x y} hx hy => iSup_Pm_lie_mem hx hy)
  have hle : Psub ≤ Z' := LieSubalgebra.lieSpan_le.mpr (fun x hx => by
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.mem_iSup_of_mem (Pi.single i 1) (SerreE_mem_Pm i))
  intro x hx
  exact hle hx

/-- **`n⁻` is the sum of its nonpositive weight pieces.** -/
lemma Msub_le_iSup_Mm : (Msub : Submodule ℂ L8) ≤ ⨆ m : Fin 8 → ℕ, Mm m := by
  let Z' : LieSubalgebra ℂ L8 :=
    LieSubalgebra.mk (⨆ m : Fin 8 → ℕ, Mm m) (fun {x y} hx hy => iSup_Mm_lie_mem hx hy)
  have hle : Msub ≤ Z' := LieSubalgebra.lieSpan_le.mpr (fun x hx => by
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.mem_iSup_of_mem (Pi.single i 1) (SerreF_mem_Mm i))
  intro x hx
  exact hle hx

/-! ## Membership in a finite supremum, and the "killer" operators -/

/-- Membership in `⨆ m ∈ s, p m` is a finite sum of members of the `p m`. -/
lemma mem_iSup_finset_iff {ι : Type*} {s : Finset ι} {p : ι → Submodule ℂ L8} {x : L8} :
    x ∈ ⨆ m ∈ s, p m ↔ ∃ f : ι → L8, (∀ m ∈ s, f m ∈ p m) ∧ x = ∑ m ∈ s, f m := by
  classical
  rw [← Finset.sup_eq_iSup]
  revert x
  induction s using Finset.induction with
  | empty =>
      intro x
      rw [Finset.sup_empty]
      constructor
      · intro hx
        exact ⟨fun _ => 0, fun m hm => absurd hm (Finset.notMem_empty m), by simpa using hx⟩
      · rintro ⟨f, -, h0⟩
        simpa using h0
  | insert a s ha ih =>
      intro x
      have hsum : ∀ (g : ι → L8), (∑ m ∈ insert a s, g m) = g a + ∑ m ∈ s, g m :=
        fun g => Finset.sum_insert ha
      rw [Finset.sup_insert, Submodule.mem_sup]
      constructor
      · rintro ⟨y, hy, z, hz, rfl⟩
        obtain ⟨f, hf, hz'⟩ := ih.mp hz
        refine ⟨Function.update f a y, ?_, ?_⟩
        · intro m hm
          rcases Finset.mem_insert.mp hm with hma | hms
          · subst hma; rw [Function.update_self]; exact hy
          · rw [Function.update_of_ne]
            exact hf m hms
            intro h; subst h; exact ha hms
        · rw [hsum, Function.update_self]
          have h1 : (∑ m ∈ s, Function.update f a y m) = ∑ m ∈ s, f m :=
            Finset.sum_congr rfl fun m hm => by
              rw [Function.update_of_ne]
              intro h; subst h; exact ha hm
          rw [h1, hz']
      · rintro ⟨f, hf, rfl⟩
        exact ⟨f a, hf a (Finset.mem_insert_self a s), ∑ m ∈ s, f m,
          ih.mpr ⟨f, fun m hm => hf m (Finset.mem_insert_of_mem hm), rfl⟩, by rw [hsum]⟩

open Classical in
/-- The "killer" operator `ad (H j) - c` acting on `e₈`. -/
noncomputable def killer (p : Fin 8 × ℂ) : Module.End ℂ L8 :=
  LieAlgebra.ad ℂ L8 (SerreH p.1) - p.2 • 1

lemma killer_apply_of_mem {ν : Fin 8 → ℂ} {x : L8} (hx : x ∈ W ν) (p : Fin 8 × ℂ) :
    killer p x = (ν p.1 - p.2) • x := by
  rw [killer, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    LieAlgebra.ad_apply, (mem_W_iff.mp hx p.1), ← sub_smul]

/-- A product of killers acts on a weight vector by the product of the scalars. -/
lemma list_prod_killer_apply (l : List (Fin 8 × ℂ)) {ν : Fin 8 → ℂ} {x : L8} (hx : x ∈ W ν) :
    (l.map killer).prod x = (l.map (fun p => ν p.1 - p.2)).prod • x := by
  induction l with
  | nil => simp
  | cons p t ih =>
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply, ih,
        killer_apply_of_mem (W_smul_mem _ hx) p, smul_smul, mul_comm]

/-- A product of killers containing a factor that kills a weight vector annihilates it. -/
lemma prod_killer_apply_eq_zero (l : List (Fin 8 × ℂ)) {ν : Fin 8 → ℂ} {x : L8} (hx : x ∈ W ν)
    (h : ∃ p ∈ l, p.2 = ν p.1) : (l.map killer).prod x = 0 := by
  rw [list_prod_killer_apply l hx]
  obtain ⟨p, hp, hp2⟩ := h
  have hz : (l.map (fun q => ν q.1 - q.2)).prod = 0 := by
    rw [List.prod_eq_zero_iff]
    exact List.mem_map.mpr ⟨p, hp, by rw [hp2, sub_self]⟩
  rw [hz, zero_smul]

/-- Two distinct weight functionals differ in some Cartan coordinate. -/
lemma exists_ne_coord {w μ : Fin 8 → ℂ} (h : w ≠ μ) : ∃ j : Fin 8, w j ≠ μ j :=
  Function.ne_iff.mp h

/-- The chosen Cartan coordinate separating `w` from `μ` (defaulting to `0` when `w = μ`). -/
noncomputable def sepCoord (μ w : Fin 8 → ℂ) : Fin 8 :=
  if h : w ≠ μ then Classical.choose (exists_ne_coord h) else 0

lemma sepCoord_spec {μ w : Fin 8 → ℂ} (h : w ≠ μ) :
    w (sepCoord μ w) ≠ μ (sepCoord μ w) := by
  rw [sepCoord, dif_pos h]
  exact Classical.choose_spec (exists_ne_coord h)

/-- The list of "killing" operators attached to a finite set of weights, aimed at the weight `μ`:
one factor for each weight `w ∈ S`, `w ≠ μ`. -/
noncomputable def killerList (μ : Fin 8 → ℂ) (S : Finset (Fin 8 → ℂ)) : List (Fin 8 × ℂ) :=
  (S.erase μ).toList.map (fun w => (sepCoord μ w, w (sepCoord μ w)))

lemma killerList_mem {μ w : Fin 8 → ℂ} {S : Finset (Fin 8 → ℂ)} (hw : w ∈ S) (hne : w ≠ μ) :
    (sepCoord μ w, w (sepCoord μ w)) ∈ killerList μ S := by
  refine List.mem_map.mpr ⟨w, ?_, rfl⟩
  rw [Finset.mem_toList, Finset.mem_erase]
  exact ⟨hne, hw⟩

lemma killerList_prod_ne_zero {μ : Fin 8 → ℂ} {S : Finset (Fin 8 → ℂ)} :
    ((killerList μ S).map (fun p => μ p.1 - p.2)).prod ≠ 0 := by
  intro h
  rw [List.prod_eq_zero_iff, List.mem_map] at h
  obtain ⟨p, hp, hp0⟩ := h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
  rw [Finset.mem_toList, Finset.mem_erase] at hw
  exact sub_ne_zero.mpr (Ne.symm (sepCoord_spec hw.1)) hp0

/-- **The killing argument.**  If every term of a finite sum lies in a weight space `W (wt i)` with
`wt i ≠ μ`, the sum cannot lie in `W μ` unless it is zero. -/
lemma killer_sum_eq_zero {ι : Type*} (s : Finset ι) (wt : ι → Fin 8 → ℂ) (y : ι → L8)
    {μ : Fin 8 → ℂ} (hne : ∀ i ∈ s, wt i ≠ μ) (hy : ∀ i ∈ s, y i ∈ W (wt i))
    (hμ : (∑ i ∈ s, y i) ∈ W μ) : ∑ i ∈ s, y i = 0 := by
  classical
  let L : List (Fin 8 × ℂ) := killerList μ (s.image wt)
  have hval : (L.map (fun p => μ p.1 - p.2)).prod ≠ 0 := killerList_prod_ne_zero
  have hT0 : (L.map killer).prod (∑ i ∈ s, y i) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    refine prod_killer_apply_eq_zero L (hy i hi)
      ⟨(sepCoord μ (wt i), wt i (sepCoord μ (wt i))), ?_, rfl⟩
    exact killerList_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩) (hne i hi)
  rw [list_prod_killer_apply L hμ] at hT0
  exact (smul_eq_zero.mp hT0).resolve_left hval

/-- **Extraction of the `μ`-component.**  In a finite sum of weight vectors with distinct weights,
the `W μ`-component is exactly the sum of the terms of weight `μ`. -/
lemma killer_extract {ι : Type*} (s : Finset ι) (wt : ι → Fin 8 → ℂ) (y : ι → L8)
    {μ : Fin 8 → ℂ} (hy : ∀ i ∈ s, y i ∈ W (wt i)) (hz : (∑ i ∈ s, y i) ∈ W μ) :
    ∑ i ∈ s, y i = ∑ i ∈ s with wt i = μ, y i := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun i => wt i = μ) y
  have hA : (∑ i ∈ s with wt i = μ, y i) ∈ W μ := by
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_filter] at hi
    simpa [hi.2] using hy i hi.1
  have hB : (∑ i ∈ s with ¬(wt i = μ), y i) ∈ W μ := by
    have h := Submodule.sub_mem _ hz hA
    rw [← hsplit, add_sub_cancel_left] at h
    exact h
  have h2 : (∑ i ∈ s with ¬(wt i = μ), y i) = 0 := by
    refine killer_sum_eq_zero (μ := μ) _ _ _ (fun i hi => ?_)
      (fun i hi => hy i (Finset.mem_of_mem_filter i hi)) hB
    exact (Finset.mem_filter.mp hi).2
  rw [← hsplit, h2, add_zero]

/-! ## The weight-`α_k` part of `n⁺` is at most one-dimensional -/

/-- Two nonnegative weights adding up to the simple root `α_k` are `0` or `α_k` themselves. -/
lemma add_ne_single {m m' : Fin 8 → ℕ} {k : Fin 8} (hm : m ≠ Pi.single k 1)
    (hm' : m' ≠ Pi.single k 1) : m + m' ≠ Pi.single k 1 := by
  intro h
  have hk : m k + m' k = 1 := by
    have := congrFun h k
    simpa using this
  have hoff : ∀ i, i ≠ k → m i = 0 ∧ m' i = 0 := by
    intro i hi
    have h1 := congrFun h i
    rw [Pi.add_apply, Pi.single_eq_of_ne' (M := fun _ => ℕ) (Ne.symm hi)] at h1
    omega
  rcases Nat.eq_zero_or_pos (m k) with h0 | hp
  · refine hm' ?_
    funext i
    by_cases hi : i = k
    · subst hi; rw [Pi.single_eq_same]; omega
    · rw [Pi.single_eq_of_ne' (M := fun _ => ℕ) (Ne.symm hi)]; exact (hoff i hi).2
  · refine hm ?_
    funext i
    by_cases hi : i = k
    · subst hi; rw [Pi.single_eq_same]; omega
    · rw [Pi.single_eq_of_ne' (M := fun _ => ℕ) (Ne.symm hi)]; exact (hoff i hi).1

lemma add_single_ne_single {m : Fin 8 → ℕ} {k : Fin 8} (hm : m ≠ 0) :
    Pi.single k 1 + m ≠ Pi.single k 1 :=
  fun h => hm (add_left_cancel (show Pi.single k 1 + m = Pi.single k 1 + 0 by rw [add_zero]; exact h))

/-- The index set of nonnegative weights different from `0` and from `α_k`. -/
abbrev IdxZ (k : Fin 8) : Type := {m : Fin 8 → ℕ // m ≠ 0 ∧ m ≠ Pi.single k 1}

/-- The sum of the nonnegative weight pieces of `n⁺` away from `0` and `α_k`. -/
noncomputable def Pmz (k : Fin 8) : Submodule ℂ L8 := ⨆ m : IdxZ k, Pm m.1

lemma iSup_Pmz_lie_mem (k : Fin 8) ⦃x y : L8⦄ (hx : x ∈ Pmz k) (hy : y ∈ Pmz k) :
    ⁅x, y⁆ ∈ Pmz k := by
  refine Submodule.iSup_induction (fun m : IdxZ k => Pm m.1)
    (motive := fun x => ∀ y, y ∈ Pmz k → ⁅x, y⁆ ∈ Pmz k) hx ?_ ?_ ?_ y hy
  · intro m x hx y hy
    refine Submodule.iSup_induction (fun m : IdxZ k => Pm m.1)
      (motive := fun y => ⁅x, y⁆ ∈ Pmz k) hy ?_ ?_ ?_
    · intro m' y hy
      refine Submodule.mem_iSup_of_mem ⟨m.1 + m'.1, ?_, ?_⟩ (bracket_mem_Pm hx hy)
      · intro h
        refine m.2.1 ?_
        funext i
        have := congrFun h i
        simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
        omega
      · exact add_ne_single m.2.2 m'.2.2
    · rw [lie_zero]; exact Submodule.zero_mem _
    · intro a b ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
  · intro y hy; rw [zero_lie]; exact Submodule.zero_mem _
  · intro a b ha hb y hy; rw [add_lie]; exact Submodule.add_mem _ (ha y hy) (hb y hy)

lemma e_k_lie_Pmz (k : Fin 8) ⦃y : L8⦄ (hy : y ∈ Pmz k) : ⁅SerreE k, y⁆ ∈ Pmz k := by
  refine Submodule.iSup_induction (fun m : IdxZ k => Pm m.1)
    (motive := fun y => ⁅SerreE k, y⁆ ∈ Pmz k) hy ?_ ?_ ?_
  · intro m y hy
    refine Submodule.mem_iSup_of_mem ⟨Pi.single k 1 + m.1, ?_, ?_⟩ ?_
    · intro h
      have := congrFun h k
      simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at this
      omega
    · exact add_single_ne_single m.2.1
    · exact bracket_mem_Pm (SerreE_mem_Pm k) hy
  · rw [lie_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb

lemma Z1_lie_mem (k : Fin 8) ⦃x y : L8⦄ (hx : x ∈ ℂ ∙ SerreE k ⊔ Pmz k)
    (hy : y ∈ ℂ ∙ SerreE k ⊔ Pmz k) : ⁅x, y⁆ ∈ ℂ ∙ SerreE k ⊔ Pmz k := by
  obtain ⟨x1, hx1, x2, hx2, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c1, rfl⟩ := Submodule.mem_span_singleton.mp hx1
  obtain ⟨c2, rfl⟩ := Submodule.mem_span_singleton.mp hy1
  have h11 : ⁅c1 • SerreE k, c2 • SerreE k⁆ = 0 := by
    rw [smul_lie, lie_smul, lie_self, smul_zero, smul_zero]
  have h12 : ⁅c1 • SerreE k, y2⁆ ∈ Pmz k := by
    rw [smul_lie]
    exact Submodule.smul_mem _ c1 (e_k_lie_Pmz k hy2)
  have h21 : ⁅x2, c2 • SerreE k⁆ ∈ Pmz k := by
    rw [lie_smul]
    refine Submodule.smul_mem _ c2 ?_
    rw [← lie_skew]
    exact (Pmz k).neg_mem (e_k_lie_Pmz k hx2)
  have h22 : ⁅x2, y2⁆ ∈ Pmz k := iSup_Pmz_lie_mem k hx2 hy2
  rw [add_lie, lie_add, lie_add, h11, zero_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_right h12)
    (Submodule.add_mem _ (Submodule.mem_sup_right h21) (Submodule.mem_sup_right h22))

/-- `n⁺` is generated by its weight pieces away from `0` and `α_k`, together with `eₖ`. -/
lemma Psub_le_Z1 (k : Fin 8) : (Psub : Submodule ℂ L8) ≤ ℂ ∙ SerreE k ⊔ Pmz k := by
  classical
  let Z' : LieSubalgebra ℂ L8 :=
    LieSubalgebra.mk (ℂ ∙ SerreE k ⊔ Pmz k) (fun {x y} hx hy => Z1_lie_mem k hx hy)
  have hle : Psub ≤ Z' := LieSubalgebra.lieSpan_le.mpr (fun x hx => by
    obtain ⟨i, rfl⟩ := hx
    by_cases hik : i = k
    · subst hik
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton.mpr ⟨1, one_smul _ _⟩)
    · refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ⟨Pi.single i 1, ?_, ?_⟩ (SerreE_mem_Pm i))
      · intro h
        have := congrFun h i
        rw [Pi.single_eq_same, Pi.zero_apply] at this
        exact one_ne_zero this
      · by_contra hne
        have h1 := congrFun hne i
        rw [Pi.single_eq_same, Pi.single_eq_of_ne' (M := fun _ => ℕ) (Ne.symm hik)] at h1
        exact one_ne_zero h1)
  intro x hx
  exact hle hx

/-- **The weight-`α_k` part of `n⁺` is spanned by `eₖ`.** -/
lemma P_inter_W_alpha_le (k : Fin 8) :
    (Psub : Submodule ℂ L8) ⊓ W (alpha k) ≤ ℂ ∙ SerreE k := by
  intro y hy
  obtain ⟨hyP, hyW⟩ := Submodule.mem_inf.mp hy
  have hyZ : y ∈ ℂ ∙ SerreE k ⊔ Pmz k := Psub_le_Z1 k hyP
  obtain ⟨y1, hy1, y2, hy2, hy12⟩ := Submodule.mem_sup.mp hyZ
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy1
  have hy2eq : y2 = y - c • SerreE k := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hy12
  have hy2W : y2 ∈ W (alpha k) := by
    rw [hy2eq]
    exact (W (alpha k)).sub_mem hyW (Submodule.smul_mem _ c (SerreE_mem_W k))
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hy2
  obtain ⟨g, hg, hgsum⟩ := mem_iSup_finset_iff.mp hs
  have hkill : y2 = 0 := by
    have h1 := killer_extract (μ := alpha k) s (fun m : IdxZ k => NWtSum m.1) g
      (fun m hm => (hg m hm).2) (by rw [← hgsum]; exact hy2W)
    have hempty : s.filter (fun m : IdxZ k => NWtSum m.1 = alpha k) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro m _ h
      exact m.2.2 (NWtSum_eq_alpha h)
    rw [← hgsum] at h1
    rw [h1, hempty, Finset.sum_empty]
  have hyc : y = c • SerreE k := by
    have := hkill
    rw [hy2eq, sub_eq_zero] at this
    exact this
  rw [hyc]
  exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩

/-- The image of the `E`-generator `eₖ` in `e₈(ℂ)` is nonzero (from the commons). -/
lemma SerreE_ne_zero (k : Fin 8) : (SerreE k : L8) ≠ 0 := e8_serreE_ne_zero k

/-- **The upper bound:** every element of the weight space of the simple root `α_k` is a multiple
of `eₖ`. -/
theorem W_alpha_le_span (k : Fin 8) : W (alpha k) ≤ ℂ ∙ SerreE k := by
  classical
  intro x hx
  -- split `x` along the triangular spanning
  have hxmem : x ∈ (Hsub : Submodule ℂ L8) ⊔ (Psub : Submodule ℂ L8) ⊔
      (Msub : Submodule ℂ L8) := by rw [span_H_P_M_top]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy
  have hxabc : x = a + b + z := by rw [← hyz, ← hab]
  -- weight decompositions of the `n⁺`- and `n⁻`-parts
  obtain ⟨sb, hsb⟩ := Submodule.mem_iSup_iff_exists_finset.mp (Psub_le_iSup_Pm hb)
  obtain ⟨fb, hfb, hbsum⟩ := mem_iSup_finset_iff.mp hsb
  obtain ⟨sc, hsc⟩ := Submodule.mem_iSup_iff_exists_finset.mp (Msub_le_iSup_Mm hz)
  obtain ⟨fc, hfc, hcsum⟩ := mem_iSup_finset_iff.mp hsc
  -- the killer list
  have hkk : CartanMatrix.E₈ k k = 2 := by fin_cases k <;> decide
  have halpha_ne_zero : alpha k ≠ 0 := by
    intro h
    have hk := congrFun h k
    simp only [alpha, Pi.zero_apply] at hk
    rw [hkk] at hk
    norm_num at hk
  have hne0 : (0 : Fin 8 → ℂ) ≠ alpha k := fun h => halpha_ne_zero h.symm
  set S : Finset (Fin 8 → ℂ) :=
    insert 0 ((sb.image NWtSum) ∪ (sc.image (fun m => -(NWtSum m)))) with hS
  have h0S : (0 : Fin 8 → ℂ) ∈ S := by rw [hS]; exact Finset.mem_insert_self 0 _
  have hbS : ∀ m ∈ sb, NWtSum m ∈ S := by
    intro m hm
    rw [hS]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr
      (Or.inl (Finset.mem_image.mpr ⟨m, hm, rfl⟩))))
  have hcS : ∀ m ∈ sc, (-(NWtSum m)) ∈ S := by
    intro m hm
    rw [hS]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr
      (Or.inr (Finset.mem_image.mpr ⟨m, hm, rfl⟩))))
  set L : List (Fin 8 × ℂ) := killerList (alpha k) S with hL
  have hval : (L.map (fun p => alpha k p.1 - p.2)).prod ≠ 0 := by
    rw [hL]; exact killerList_prod_ne_zero
  have hTx : (L.map killer).prod x = (L.map (fun p => alpha k p.1 - p.2)).prod • x := by
    rw [hL]; exact list_prod_killer_apply L hx
  -- the `H`-part is killed
  have hTa : (L.map killer).prod a = 0 := by
    refine prod_killer_apply_eq_zero L (Hsub_le_W_zero ha)
      ⟨(sepCoord (alpha k) 0, (0 : Fin 8 → ℂ) (sepCoord (alpha k) 0)), ?_, rfl⟩
    rw [hL]
    exact killerList_mem h0S hne0
  -- the `n⁺`-part: only the `α_k`-component survives
  have hTb : (L.map killer).prod b
      = (L.map (fun p => alpha k p.1 - p.2)).prod •
        (∑ m ∈ sb with NWtSum m = alpha k, fb m) := by
    rw [hbsum, map_sum, Finset.smul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    by_cases hh : NWtSum m = alpha k
    · rw [if_pos hh, list_prod_killer_apply L (hfb m hm).2]
      congr 1
      rw [hh]
    · rw [if_neg hh]
      refine prod_killer_apply_eq_zero L ((hfb m hm).2)
        ⟨(sepCoord (alpha k) (NWtSum m), NWtSum m (sepCoord (alpha k) (NWtSum m))), ?_, rfl⟩
      rw [hL]
      exact killerList_mem (hbS m hm) hh
  -- the `n⁻`-part is killed
  have hTz : (L.map killer).prod z = 0 := by
    rw [hcsum, map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    refine prod_killer_apply_eq_zero L ((hfc m hm).2)
      ⟨(sepCoord (alpha k) (-(NWtSum m)), (-(NWtSum m)) (sepCoord (alpha k) (-(NWtSum m)))),
        ?_, rfl⟩
    rw [hL]
    exact killerList_mem (hcS m hm) (neg_NWtSum_ne_alpha m k)
  -- assemble
  have hTx' : (L.map killer).prod x
      = (L.map killer).prod a + (L.map killer).prod b + (L.map killer).prod z := by
    rw [hxabc, map_add, map_add]
  have hkey : (L.map (fun p => alpha k p.1 - p.2)).prod • x
      = (L.map (fun p => alpha k p.1 - p.2)).prod •
        (∑ m ∈ sb with NWtSum m = alpha k, fb m) := by
    rw [← hTx, hTx', hTa, hTb, hTz, zero_add, add_zero]
  have hxsum : x = ∑ m ∈ sb with NWtSum m = alpha k, fb m := by
    have h := congrArg
      (fun w => ((L.map (fun p => alpha k p.1 - p.2)).prod)⁻¹ • w) hkey
    simpa [smul_smul, inv_mul_cancel₀ hval] using h
  -- the surviving term lies in the weight-`α_k` part of `n⁺`
  have hxPm : x ∈ Pm (Pi.single k 1) := by
    rw [hxsum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [Finset.mem_filter] at hm
    obtain ⟨hm1, hm2⟩ := hm
    have hmk : m = Pi.single k 1 := NWtSum_eq_alpha hm2
    simpa [hmk] using hfb m hm1
  exact P_inter_W_alpha_le k ⟨hxPm.1, hx⟩

/-- The (joint) weight space of the Serre-constructed `e₈` at a **simple root** is one-dimensional.

Here `μ : Fin 8 → ℤ` records the eigenvalues of the eight commuting operators `ad (H i)`, so the
weight space of `μ` is `⨅ i, ker (ad (H i) - μ i)`.  A simple root `α_k` has coordinates
`⟨α_k, α_j∨⟩ = A k j` (the `k`-th row of the Cartan matrix), which is why the statement uses
`fun i => CartanMatrix.E₈ k i`. -/

theorem e8_simple_root_weightSpace_finrank_compat (k : Fin 8) :
    Module.finrank ℂ ↥(⨅ i : Fin 8, (LinearMap.ker (LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ)
      (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
        (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i))) - ((CartanMatrix.E₈ k i : ℤ) : ℂ) • 1) :
        Submodule ℂ (LieAlgebra.e₈ ℂ))) = 1 := by
  have hWeq : (⨅ i : Fin 8, (LinearMap.ker (LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ)
      (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
        (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i))) - ((CartanMatrix.E₈ k i : ℤ) : ℂ) • 1) :
        Submodule ℂ (LieAlgebra.e₈ ℂ))) = W (alpha k) := rfl
  rw [hWeq]
  have hge : ℂ ∙ SerreE k ≤ W (alpha k) :=
    Submodule.span_le.mpr (by rintro x rfl; exact SerreE_mem_W k)
  rw [le_antisymm (W_alpha_le_span k) hge]
  exact finrank_span_singleton (SerreE_ne_zero k)

end Commons.Algebra.Lie.SerreConstruction
