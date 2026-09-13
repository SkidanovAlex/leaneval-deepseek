import Mathlib
import Submission.Grassmann.EOp
import Submission.Commons.LinearAlgebra.Matrix.mul_eq_zero_iff_range_le_ker

/-!
# The combinatorial Laplacian `𝓔_v` on `L(V,W)` (arXiv:2209.04243, §5.6, Lemma 5.3)

For a nonzero vector `v ∈ V` the paper defines the *combinatorial Laplacian*
`𝓔_v[f] = 𝔼_{V' ∌ v}[𝔢_{V/V'}[f]]`, the average of the averaging operators `𝔢` over the
hyperplanes `V'` of `V` that do not contain `v`.  Equivalently (over `𝔽₂`, where a hyperplane
avoiding `v` is the kernel of a unique linear functional `φ` with `φ v = 1`),

  `eOpV v f = 𝔼_{φ : φ v = 1} 𝔢_{ker φ}`.

The main result is the **Fourier formula** (Lemma 5.3):

  `eOpV v (mchar X) = (1 - [v ∈ range X]) • 2^{-rank X} • mchar X`.

The proof of the multiplier uses only two facts: the set `{φ : φ v = 1}` is a coset of
`{ψ : ψ v = 0}` (so it has `2^{n-1}` elements and shifts act on it), and the character
`u ↦ (-1)^{φ u}` summed over that coset is `2^{n-1} [u = 0] - 2^{n-1}[u = v]`.
-/

open Finset BigOperators
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

variable {m n : ℕ}

/-! ## The row matrix of a functional -/

/-- The `1 × n` matrix of a linear functional, with respect to the standard basis. -/
def linRow (φ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) : Matrix (Fin 1) (Fin n) (ZMod 2) :=
  fun _ j => φ (Pi.single j 1)

/-- Every vector is the sum of its coordinates times the standard basis vectors. -/
lemma sum_single_smul (x : Fin n → ZMod 2) :
    (∑ i : Fin n, x i • Pi.single i (1 : ZMod 2)) = x := by
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro i _ hij
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hij), smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

lemma linRow_mulVec (φ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (x : Fin n → ZMod 2) :
    Matrix.mulVec (linRow φ) x 0 = φ x := by
  rw [Matrix.mulVec_apply_eq_sum]
  have h1 : (∑ j : Fin n, linRow φ 0 j * x j) =
      ∑ j : Fin n, φ (x j • Pi.single j (1 : ZMod 2)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [linRow, map_smul, smul_eq_mul, mul_comm]
  rw [h1, ← map_sum φ, sum_single_smul]

lemma ker_mulVecLin_linRow (φ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    LinearMap.ker (Matrix.mulVecLin (linRow φ)) = LinearMap.ker φ := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h
    have h0 : Matrix.mulVec (linRow φ) x 0 = 0 := congrFun h 0
    rwa [linRow_mulVec] at h0
  · intro h
    funext i
    rw [show i = (0 : Fin 1) from Subsingleton.elim i 0, linRow_mulVec, h]
    rfl

/-- **The Fourier formula for `𝔢_{ker φ}`**: the averaging operator for the functional `φ`
keeps precisely the characters whose image lies in `ker φ`. -/
theorem eOp_linRow_mchar (φ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (X : Matrix (Fin n) (Fin m) (ZMod 2)) (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    eOp (linRow φ) (mchar X) A =
      if LinearMap.range (Matrix.mulVecLin X) ≤ LinearMap.ker φ then mchar X A else 0 := by
  rw [eOp_mchar]
  have hiff : linRow φ * X = 0 ↔
      LinearMap.range (Matrix.mulVecLin X) ≤ LinearMap.ker φ := by
    rw [Commons.LinearAlgebra.Matrix.mul_eq_zero_iff_range_le_ker, ker_mulVecLin_linRow]
  by_cases h : linRow φ * X = 0
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]

/-! ## Counting linear functionals with a prescribed value -/

/-- Every element of `𝔽₂` is `0` or `1`. -/
lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-- The kernel of a nonzero `𝔽₂`-valued linear functional on a finite-dimensional space has
`2^{dim - 1}` elements. -/
lemma natCard_ker_ne_zero {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] (f : W →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) :
    Nat.card (LinearMap.ker f) = 2 ^ (Module.finrank (ZMod 2) W - 1) := by
  have hfr : Module.finrank (ZMod 2) ↥(LinearMap.range f) = 1 := by
    have hne : LinearMap.range f ≠ ⊥ := by
      intro h
      exact hf (LinearMap.range_eq_bot.mp h)
    have hpos : 0 < Module.finrank (ZMod 2) ↥(LinearMap.range f) :=
      Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h)
    have hle : Module.finrank (ZMod 2) ↥(LinearMap.range f) ≤ 1 := by
      have h1 := Submodule.finrank_mono (show LinearMap.range f ≤ ⊤ from le_top)
      rwa [finrank_top, Module.finrank_self] at h1
    omega
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hfr] at hrn
  have hker : Module.finrank (ZMod 2) ↥(LinearMap.ker f) = Module.finrank (ZMod 2) W - 1 := by
    omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.ker f)), hker,
    Nat.card_eq_fintype_card, ZMod.card]

/-- Evaluation at `v`, as a linear functional on the dual. -/
def evalDual {n : ℕ} (v : Fin n → ZMod 2) :
    Module.Dual (ZMod 2) (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.applyₗ (M := Fin n → ZMod 2) (M₂ := ZMod 2) v

lemma evalDual_apply {n : ℕ} (v : Fin n → ZMod 2) (φ : Module.Dual (ZMod 2) (Fin n → ZMod 2)) :
    evalDual v φ = φ v := rfl

lemma finrank_dual_fin {n : ℕ} :
    Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Fin n → ZMod 2)) = n := by
  rw [Module.finrank_linearMap (ZMod 2) (ZMod 2), Module.finrank_fintype_fun_eq_card,
    Module.finrank_self, mul_one, Fintype.card_fin]

lemma evalDual_ne_zero {n : ℕ} (v : Fin n → ZMod 2) (hv : v ≠ 0) : evalDual v ≠ 0 := by
  intro h
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hv
  have h' : evalDual v φ = 0 := DFunLike.congr_fun h φ
  rw [evalDual_apply, hφ] at h'
  exact one_ne_zero h'

/-- The kernel of the evaluation map has `2^{n-1}` elements. -/
lemma natCard_ker_evalDual {n : ℕ} (v : Fin n → ZMod 2) (hv : v ≠ 0) :
    Nat.card (LinearMap.ker (evalDual v)) = 2 ^ (n - 1) := by
  have h := natCard_ker_ne_zero (evalDual v) (evalDual_ne_zero v hv)
  rwa [finrank_dual_fin] at h

/-- The number of linear functionals taking the value `1` at a nonzero vector `v` is
`2^{n-1}`. -/
lemma natCard_evalDual_eq_one {n : ℕ} (v : Fin n → ZMod 2) (hv : v ≠ 0) :
    Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // evalDual v φ = 1} = 2 ^ (n - 1) := by
  obtain ⟨φ₀, hφ₀⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hv
  have he : Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // evalDual v φ = 1} =
      Nat.card {ψ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // evalDual v ψ = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.addRight φ₀) ?_)
    intro φ
    show evalDual v φ = 1 ↔ evalDual v (φ + φ₀) = 0
    rw [map_add, evalDual_apply v φ, evalDual_apply v φ₀, hφ₀]
    constructor
    · intro h
      rw [h]
      exact CharTwo.add_self_eq_zero 1
    · intro h
      rw [add_eq_zero_iff_eq_neg] at h
      rw [h, CharTwo.neg_eq]
  rw [he]
  exact natCard_ker_evalDual v hv

/-- The number of linear functionals taking the value `1` at a nonzero vector `v` is
`2^{n-1}`. -/
lemma natCard_dual_apply_eq_one {n : ℕ} (v : Fin n → ZMod 2) (hv : v ≠ 0) :
    Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // φ v = 1} = 2 ^ (n - 1) := by
  have h : {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // φ v = 1} ≃
      {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // evalDual v φ = 1} :=
    Equiv.subtypeEquivRight (fun φ => by rw [evalDual_apply])
  rw [Nat.card_congr h]
  exact natCard_evalDual_eq_one v hv

/-! ## The annihilator and the counting lemma with a subspace condition -/

lemma le_ker_iff_mem_dualAnnihilator {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (φ : Module.Dual (ZMod 2) (Fin n → ZMod 2)) :
    U ≤ LinearMap.ker φ ↔ φ ∈ U.dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  exact forall₂_congr fun x _ => LinearMap.mem_ker

lemma finrank_dualAnnihilator {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Module.finrank (ZMod 2) ↥(U.dualAnnihilator) = n - Module.finrank (ZMod 2) U := by
  have h1 := (Subspace.quotEquivAnnihilator (K := ZMod 2) (V := Fin n → ZMod 2) U).finrank_eq
  have h2 := Submodule.finrank_quotient_add_finrank U
  have h3 : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [h3] at h2
  omega

/-- Fibers of an `𝔽₂`-valued linear functional that are nonempty have the cardinality of the
kernel. -/
lemma natCard_fiber_one_eq_natCard_ker {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (g : W →ₗ[ZMod 2] ZMod 2) (hb : ∃ x, g x = 1) :
    Nat.card {x : W // g x = 1} = Nat.card (LinearMap.ker g) := by
  obtain ⟨x₀, hx₀⟩ := hb
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.addRight x₀) ?_)
  intro x
  show g x = 1 ↔ g (x + x₀) = 0
  rw [map_add, hx₀]
  constructor
  · intro h; rw [h]; exact CharTwo.add_self_eq_zero 1
  · intro h
    rw [add_eq_zero_iff_eq_neg] at h
    rw [h, CharTwo.neg_eq]

/-- **The counting lemma underlying the Fourier formula for the combinatorial Laplacian**:
the number of functionals `φ` with `φ v = 1` and `U ≤ ker φ` is `2^{n - dim U - 1}`, provided
`v ∉ U`. -/
lemma natCard_evalDual_eq_one_of_le_ker {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (v : Fin n → ZMod 2) (hv : v ∉ U) :
    Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // U ≤ LinearMap.ker φ ∧ φ v = 1}
      = 2 ^ (n - Module.finrank (ZMod 2) U - 1) := by
  classical
  obtain ⟨f, hfv, hfU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := U) hv
    (inferInstance : Module.Projective (ZMod 2) ((Fin n → ZMod 2) ⧸ U))
  have hfker : U ≤ LinearMap.ker f := by
    rw [← Submodule.comap_bot f]
    exact (Submodule.map_le_iff_le_comap).mp hfU.le
  have hf1 : f v = 1 := by
    rcases zmod2_eq_zero_or_one (f v) with h | h
    · exact absurd h hfv
    · exact h
  set A : Submodule (ZMod 2) (Module.Dual (ZMod 2) (Fin n → ZMod 2)) := U.dualAnnihilator
    with hA
  set g : ↥A →ₗ[ZMod 2] ZMod 2 := (evalDual v).comp A.subtype with hg
  have hfA : f ∈ A := (le_ker_iff_mem_dualAnnihilator U f).mp hfker
  have hgf : g ⟨f, hfA⟩ = f v := rfl
  have hb : ∃ x : ↥A, g x = 1 := ⟨⟨f, hfA⟩, by rw [hgf, hf1]⟩
  have hgne : g ≠ 0 := by
    intro h
    have h' : g ⟨f, hfA⟩ = 0 := DFunLike.congr_fun h ⟨f, hfA⟩
    rw [hgf, hf1] at h'
    exact one_ne_zero h'
  have e1 : {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // U ≤ LinearMap.ker φ ∧ φ v = 1}
      ≃ {x : ↥A // g x = 1} :=
    (Equiv.subtypeEquivRight (fun φ => by
      rw [le_ker_iff_mem_dualAnnihilator U φ, evalDual_apply])).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) =>
          φ ∈ A) (fun φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) => evalDual v φ = 1)).symm
  rw [Nat.card_congr e1, natCard_fiber_one_eq_natCard_ker g hb,
    natCard_ker_ne_zero g hgne, finrank_dualAnnihilator]

/-! ## The combinatorial Laplacian `𝓔_v` and its Fourier formula -/

instance instFiniteDual (n : ℕ) : Finite (Module.Dual (ZMod 2) (Fin n → ZMod 2)) :=
  Finite.of_injective
    (fun f : Module.Dual (ZMod 2) (Fin n → ZMod 2) => (f : (Fin n → ZMod 2) → ZMod 2))
    (fun _ _ h => LinearMap.ext fun x => congrFun h x)

noncomputable instance instFintypeDual (n : ℕ) :
    Fintype (Module.Dual (ZMod 2) (Fin n → ZMod 2)) :=
  Fintype.ofFinite _

/-- The **combinatorial Laplacian** `𝓔_v`: the average of the operators `𝔢_{ker φ}` over the
linear functionals `φ` with `φ v = 1`. -/
def eOpV {m n : ℕ} (v : Fin n → ZMod 2)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ :=
  ((Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // φ v = 1} : ℂ))⁻¹ •
    ∑ φ : {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // φ v = 1}, eOp (linRow φ.1) f

lemma natCard_subtype_subtype_eq {α : Type*} (p q : α → Prop) :
    Nat.card {x : {a // p a} // q x.1} = Nat.card {a // p a ∧ q a} :=
  Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p q)

/-- The number of functionals with `φ v = 1` and `U ≤ ker φ`. -/
lemma natCard_dual_apply_eq_one_and_le_ker {n : ℕ}
    (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
    Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) //
        φ v = 1 ∧ U ≤ LinearMap.ker φ} =
      if v ∈ U then 0 else 2 ^ (n - Module.finrank (ZMod 2) U - 1) := by
  by_cases hv : v ∈ U
  · rw [if_pos hv]
    haveI : IsEmpty {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) //
        φ v = 1 ∧ U ≤ LinearMap.ker φ} :=
      ⟨fun x => by
        have h1 : x.1 v = 0 := x.2.2 hv
        rw [x.2.1] at h1
        exact one_ne_zero h1⟩
    exact Nat.card_eq_zero.mpr (Or.inl ‹IsEmpty _›)
  · rw [if_neg hv]
    have h : Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) //
          φ v = 1 ∧ U ≤ LinearMap.ker φ} =
        Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) //
          U ≤ LinearMap.ker φ ∧ φ v = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) =>
        and_comm))
    rw [h]
    exact natCard_evalDual_eq_one_of_le_ker U v hv

/-- **Lemma 5.3 of arXiv:2209.04243**: the Fourier multiplier of the combinatorial Laplacian.
The character `mchar X` is kept, with multiplier `2^{-rank X}`, unless `v` lies in the image
of `X`, in which case it is killed. -/
theorem eOpV_mchar {m n : ℕ} (v : Fin n → ZMod 2) (hv : v ≠ 0)
    (X : Matrix (Fin n) (Fin m) (ZMod 2)) (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    eOpV v (mchar X) A = (if v ∈ LinearMap.range (Matrix.mulVecLin X) then 0
      else ((2 : ℂ) ^ X.rank)⁻¹) * mchar X A := by
  classical
  set U : Submodule (ZMod 2) (Fin n → ZMod 2) := LinearMap.range (Matrix.mulVecLin X) with hU
  have hsum : (∑ φ : {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // φ v = 1},
        eOp (linRow φ.1) (mchar X) A) =
      (Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) //
        φ v = 1 ∧ U ≤ LinearMap.ker φ} : ℂ) * mchar X A := by
    have hterm : ∀ φ : {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // φ v = 1},
        eOp (linRow φ.1) (mchar X) A
          = (if U ≤ LinearMap.ker φ.1 then (1 : ℂ) else 0) * mchar X A := by
      intro φ
      rw [eOp_linRow_mchar]
      by_cases h : U ≤ LinearMap.ker φ.1
      · rw [if_pos h, if_pos h, one_mul]
      · rw [if_neg h, if_neg h, zero_mul]
    rw [Finset.sum_congr rfl (fun φ _ => hterm φ), ← Finset.sum_mul, Finset.sum_boole]
    congr 1
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact_mod_cast Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) => φ v = 1)
      (fun φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) => U ≤ LinearMap.ker φ))
  have hcard := natCard_dual_apply_eq_one v hv
  have hne : Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // φ v = 1} ≠ 0 := by
    rw [hcard]; exact pow_ne_zero _ (by norm_num)
  have hcast : (Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // φ v = 1} : ℂ) =
      (2 : ℂ) ^ (n - 1) := by
    rw [hcard]; push_cast; ring
  rw [eOpV]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, hsum, hcast]
  rw [natCard_dual_apply_eq_one_and_le_ker U v]
  by_cases hvU : v ∈ U
  · rw [if_pos hvU, if_pos hvU]
    ring
  · rw [if_neg hvU, if_neg hvU]
    have hfin : Module.finrank (ZMod 2) U = X.rank := rfl
    rw [hfin]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    have hr : X.rank ≤ n - 1 := by
      by_contra h
      have hfull : X.rank = n := by
        have hle : X.rank ≤ n := by
          have h := Submodule.finrank_mono (show U ≤ ⊤ from le_top)
          rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
          rwa [hfin] at h
        omega
      have hUtop : U = ⊤ := Submodule.eq_top_of_finrank_eq (by
        rw [hfin, hfull, Module.finrank_fintype_fun_eq_card, Fintype.card_fin])
      exact hvU (by rw [hUtop]; exact Submodule.mem_top)
    have hpow : ((2 : ℂ) ^ (n - 1))⁻¹ * (2 : ℂ) ^ (n - X.rank - 1) =
        ((2 : ℂ) ^ X.rank)⁻¹ := by
      have h1 : n - X.rank - 1 = n - 1 - X.rank := by omega
      have hne2 : ((2 : ℂ) ^ (n - 1 - X.rank)) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hsplit : (2 : ℂ) ^ (n - 1) =
          (2 : ℂ) ^ X.rank * (2 : ℂ) ^ (n - 1 - X.rank) := by
        rw [← pow_add]; congr 1; omega
      rw [h1, hsplit, mul_inv]
      rw [show ((2 : ℂ) ^ X.rank)⁻¹ * ((2 : ℂ) ^ (n - 1 - X.rank))⁻¹ *
            (2 : ℂ) ^ (n - 1 - X.rank)
          = ((2 : ℂ) ^ X.rank)⁻¹ * (((2 : ℂ) ^ (n - 1 - X.rank))⁻¹ *
            (2 : ℂ) ^ (n - 1 - X.rank)) by ring,
        inv_mul_cancel₀ hne2, mul_one]
    rw [show ((2 : ℂ) ^ (n - 1))⁻¹ * ((2 : ℂ) ^ (n - X.rank - 1) * mchar X A)
        = (((2 : ℂ) ^ (n - 1))⁻¹ * (2 : ℂ) ^ (n - X.rank - 1)) * mchar X A by ring]
    rw [hpow]

end

end Submission.Grassmann
