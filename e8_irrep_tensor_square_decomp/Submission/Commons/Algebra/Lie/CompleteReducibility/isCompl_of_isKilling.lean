import Mathlib
import Submission.Commons.Algebra.Lie.Casimir.lie_commute
import Submission.Commons.Algebra.Lie.CartanCriterion.traceForm_nondegenerate
import Submission.Commons.Algebra.Lie.Semisimple.lie_self_ideal
import Submission.Commons.Algebra.Lie.Semisimple.hasTrivialRadical_ideal
import Submission.Commons.Algebra.Lie.Killing.moduleFinite
import Submission.Commons.Algebra.Lie.CompleteReducibility.exists_isCompl_of_triv_quotient_univ

open LinearMap (trace)

namespace Commons.Algebra.Lie.CompleteReducibility

/-!
# Weyl's complete reducibility theorem

This file proves that every Lie submodule of a finite-dimensional module over a Lie algebra with
non-degenerate Killing form admits a Lie submodule complement.

The proof follows the classical "Casimir" argument (see e.g. Humphreys, *Introduction to Lie
Algebras and Representation Theory*, §6.2--6.3, or Akhil Mathew's exposition):

* If `L` has non-degenerate Killing form then `L` is semisimple, hence a direct sum of simple
  ideals, and every ideal of `L` is perfect (equals its own derived ideal) with trivial radical.
* Let `N ⊆ M` be a Lie submodule. Using the Lie module structure on `End_K(M)`, one finds an
  `L`-invariant `K`-linear map `P : M → M` with `P(M) ⊆ N` and `P|_N = id`; then `ker P` is a
  complement. Producing `P` reduces (via a maximality/averaging argument) to splitting extensions
  `0 → W → V → k → 0` with trivial quotient.
* For such an extension with `W` simple and non-trivial one uses the Casimir operator of the trace
  form of `W`; its trace is `dim W`, which is non-zero in characteristic zero.

## Main result

* `isCompl_of_isKilling`
-/

section Casimir

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- The **Casimir operator** attached to a basis `b` of `L` and the dual basis with respect to a
non-degenerate bilinear form `B` (e.g. the trace form of a module, or the Killing form). -/
noncomputable def casimirOp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K L) (hB : B.Nondegenerate) (b : Module.Basis ι K L) : M →ₗ[K] M :=
  ∑ i, LieModule.toEnd K L M (b i) ∘ₗ LieModule.toEnd K L M (B.dualBasis hB b i)

lemma toEnd_lie (x y : L) :
    LieModule.toEnd K L M ⁅x, y⁆
      = LieModule.toEnd K L M x ∘ₗ LieModule.toEnd K L M y
        - LieModule.toEnd K L M y ∘ₗ LieModule.toEnd K L M x := by
  ext m
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LieModule.toEnd_apply_apply]
  rw [leibniz_lie]
  abel

lemma sum_smul_comp {ι : Type*} [Fintype ι] (c : ι → K) (g : ι → M →ₗ[K] M) (h : M →ₗ[K] M) :
    (∑ i, c i • g i) ∘ₗ h = ∑ i, c i • (g i ∘ₗ h) := by
  ext; simp [LinearMap.comp_apply, Finset.sum_apply]

lemma comp_sum_smul {ι : Type*} [Fintype ι] (h : M →ₗ[K] M) (c : ι → K) (g : ι → M →ₗ[K] M) :
    h ∘ₗ (∑ i, c i • g i) = ∑ i, c i • (h ∘ₗ g i) := by
  ext; simp [LinearMap.comp_apply, Finset.sum_apply]

lemma sum_comp_lin {ι : Type*} [Fintype ι] (f : ι → M →ₗ[K] M) (g : M →ₗ[K] M) :
    (∑ i, f i) ∘ₗ g = ∑ i, f i ∘ₗ g := by
  ext; simp [LinearMap.comp_apply, Finset.sum_apply]

lemma comp_sum_lin {ι : Type*} [Fintype ι] (f : M →ₗ[K] M) (g : ι → M →ₗ[K] M) :
    f ∘ₗ (∑ i, g i) = ∑ i, f ∘ₗ g i := by
  ext; simp [LinearMap.comp_apply, Finset.sum_apply]

lemma sum_apply_lin {ι : Type*} [Fintype ι] (f : ι → M →ₗ[K] M) (v : M) :
    (∑ i, f i) v = ∑ i, f i v := by simp

lemma toEnd_repr_dual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K L) (b : Module.Basis ι K L) (f : ι → L)
    (hb : ∀ i j, B (b i) (f j) = if i = j then 1 else 0) (v : L) :
    LieModule.toEnd K L M v = ∑ j, B v (f j) • LieModule.toEnd K L M (b j) := by
  conv_lhs => rw [Commons.Algebra.Lie.Casimir.repr_dual B b f hb v]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]

lemma toEnd_repr_dual' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K L) (b : Module.Basis ι K L) (f : ι → L)
    (hb : ∀ i j, B (b i) (f j) = if i = j then 1 else 0)
    (hb' : ∀ i j, B (f i) (b j) = if i = j then 1 else 0) (v : L) :
    LieModule.toEnd K L M v = ∑ j, B v (b j) • LieModule.toEnd K L M (f j) := by
  conv_lhs => rw [Commons.Algebra.Lie.Casimir.repr_dual' B b f hb hb' v]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]

/-- The Casimir operator is `L`-equivariant: it commutes with the action of `L` on `M`. -/
lemma casimirOp_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K L) (hBsym : B.IsSymm) (hBinv : B.lieInvariant L)
    (hB : B.Nondegenerate) (b : Module.Basis ι K L) (x : L) :
    LieModule.toEnd K L M x ∘ₗ casimirOp B hB b
      = casimirOp B hB b ∘ₗ LieModule.toEnd K L M x := by
  obtain ⟨f, hfdef⟩ : ∃ f : ι → L, f = fun i => B.dualBasis hB b i := ⟨_, rfl⟩
  have hbd : casimirOp B hB b = ∑ i, LieModule.toEnd K L M (b i) ∘ₗ
      LieModule.toEnd K L M (f i) := by
    rw [show casimirOp B hB b = ∑ i, LieModule.toEnd K L M (b i) ∘ₗ
      LieModule.toEnd K L M (B.dualBasis hB b i) from rfl]
    exact Finset.sum_congr rfl fun i _ => by rw [hfdef]
  have hb : ∀ i j, B (b i) (f j) = if i = j then 1 else 0 := by
    intro i j; rw [hfdef]
    exact B.apply_dualBasis_right hB hBsym b i j
  have hb' : ∀ i j, B (f i) (b j) = if i = j then 1 else 0 := by
    intro i j; rw [hfdef, B.apply_dualBasis_left hB b i j]
    by_cases h : i = j <;> simp [h, eq_comm]
  have hE : ∀ A B C : M →ₗ[K] M, A ∘ₗ (B ∘ₗ C) - (B ∘ₗ C) ∘ₗ A
      = (A ∘ₗ B - B ∘ₗ A) ∘ₗ C + B ∘ₗ (A ∘ₗ C - C ∘ₗ A) := by
    intro A B C
    have key : (A : Module.End K M) * (B * C) - (B * C) * A
        = (A * B - B * A) * C + B * (A * C - C * A) := by noncomm_ring
    simpa only [Module.End.mul_eq_comp, LinearMap.sub_comp, LinearMap.comp_sub,
      LinearMap.comp_add, LinearMap.add_comp] using key
  have key : LieModule.toEnd K L M x ∘ₗ casimirOp B hB b
      - casimirOp B hB b ∘ₗ LieModule.toEnd K L M x
      = ∑ i, (LieModule.toEnd K L M ⁅x, b i⁆ ∘ₗ LieModule.toEnd K L M (f i)
              + LieModule.toEnd K L M (b i) ∘ₗ LieModule.toEnd K L M ⁅x, f i⁆) := by
    rw [hbd, comp_sum_lin, sum_comp_lin, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [toEnd_lie x (b i), toEnd_lie x (f i)]
    exact hE _ _ _
  have h1a : (∑ i, LieModule.toEnd K L M ⁅x, b i⁆ ∘ₗ LieModule.toEnd K L M (f i))
      = ∑ i, ∑ j, B ⁅x, b i⁆ (f j) •
          (LieModule.toEnd K L M (b j) ∘ₗ LieModule.toEnd K L M (f i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [toEnd_repr_dual B b f hb ⁅x, b i⁆, sum_smul_comp]
  have h1 : (∑ i, LieModule.toEnd K L M ⁅x, b i⁆ ∘ₗ LieModule.toEnd K L M (f i))
      = ∑ j, ∑ i, B ⁅x, b i⁆ (f j) •
          (LieModule.toEnd K L M (b j) ∘ₗ LieModule.toEnd K L M (f i)) := by
    rw [h1a, Finset.sum_comm]
  have h2a : (∑ i, LieModule.toEnd K L M (b i) ∘ₗ LieModule.toEnd K L M ⁅x, f i⁆)
      = ∑ i, ∑ j, B ⁅x, f i⁆ (b j) •
          (LieModule.toEnd K L M (b i) ∘ₗ LieModule.toEnd K L M (f j)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [toEnd_repr_dual' B b f hb hb' ⁅x, f i⁆, comp_sum_smul]
  have h2 : (∑ i, LieModule.toEnd K L M (b i) ∘ₗ LieModule.toEnd K L M ⁅x, f i⁆)
      = ∑ j, ∑ i, B ⁅x, f j⁆ (b i) •
          (LieModule.toEnd K L M (b j) ∘ₗ LieModule.toEnd K L M (f i)) := by
    rw [h2a, Finset.sum_comm]
  have hsum : (∑ i, (LieModule.toEnd K L M ⁅x, b i⁆ ∘ₗ LieModule.toEnd K L M (f i)
              + LieModule.toEnd K L M (b i) ∘ₗ LieModule.toEnd K L M ⁅x, f i⁆)) = 0 := by
    rw [Finset.sum_add_distrib]
    rw [h1, h2, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    have hcancel : B ⁅x, b i⁆ (f j) + B ⁅x, f j⁆ (b i) = 0 := by
      rw [hBinv x (b i) (f j), ← hBsym.eq (b i) ⁅x, f j⁆, neg_add_cancel]
    rw [← add_smul, hcancel, zero_smul]
  have hzero : LieModule.toEnd K L M x ∘ₗ casimirOp B hB b
      - casimirOp B hB b ∘ₗ LieModule.toEnd K L M x = 0 := by rw [key, hsum]
  exact sub_eq_zero.mp hzero

/-- The trace of the Casimir operator attached to `B` equals the sum of the values of `B` on the
basis and its dual basis. -/
lemma trace_casimirOp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K L) (hB : B.Nondegenerate)
    (hBt : ∀ x y : L, B x y
      = (trace K M) (LieModule.toEnd K L M x ∘ₗ LieModule.toEnd K L M y))
    (b : Module.Basis ι K L) :
    trace K M (casimirOp B hB b) = ∑ i, B (b i) (B.dualBasis hB b i) := by
  rw [show casimirOp B hB b = ∑ i, LieModule.toEnd K L M (b i) ∘ₗ
      LieModule.toEnd K L M (B.dualBasis hB b i) from rfl]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => (hBt (b i) (B.dualBasis hB b i)).symm

/-- The trace of the Casimir operator of the trace form of a module is the dimension of the
Lie algebra. -/
lemma trace_casimirOp_traceForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hB : (LieModule.traceForm K L M).Nondegenerate) (b : Module.Basis ι K L) :
    trace K M (casimirOp (LieModule.traceForm K L M) hB b) = (Fintype.card ι : K) := by
  rw [trace_casimirOp (LieModule.traceForm K L M) hB
    (fun x y => (LieModule.traceForm_apply_apply K L M x y).symm) b]
  have hsym : (LieModule.traceForm K L M).IsSymm :=
    LinearMap.BilinForm.isSymm_iff.mpr (LieModule.traceForm_isSymm K L M)
  have h : ∀ i, (LieModule.traceForm K L M) (b i)
      ((LieModule.traceForm K L M).dualBasis hB b i) = (1 : K) := by
    intro i
    rw [(LieModule.traceForm K L M).apply_dualBasis_right hB hsym b i i]
    simp
  simp [h]

/-- The Casimir operator on a module restricts to the Casimir operator on a Lie submodule. -/
lemma casimirOp_coe {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K L) (hB : B.Nondegenerate) (b : Module.Basis ι K L)
    (N : LieSubmodule K L M) (x : N) :
    casimirOp (M := M) B hB b (x : M) = (casimirOp (M := N) B hB b x : N) := by
  simp only [casimirOp]
  simp

end Casimir

section CasimirHom

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- The Casimir operator packaged as a morphism of Lie modules, using that it commutes with the
action (centrality of the Casimir element). -/
noncomputable def casimirHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K L) (hBsym : B.IsSymm) (hBinv : B.lieInvariant L)
    (hB : B.Nondegenerate) (b : Module.Basis ι K L) : M →ₗ⁅K,L⁆ M :=
  { casimirOp B hB b with
    map_lie' := by
      intro x m
      have h := LinearMap.congr_fun (casimirOp_comm B hBsym hBinv hB b x) m
      simpa using h.symm }

@[simp] lemma casimirHom_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K L) (hBsym : B.IsSymm) (hBinv : B.lieInvariant L)
    (hB : B.Nondegenerate) (b : Module.Basis ι K L) (m : M) :
    casimirHom B hBsym hBinv hB b m = casimirOp B hB b m := rfl

end CasimirHom

section Faithful

variable {K h V : Type*} [Field K] [CharZero K] [LieRing h] [LieAlgebra K h]
  [AddCommGroup V] [Module K V] [LieRingModule h V] [LieModule K h V]
  [Module.Finite K h] [Nontrivial h] [Module.Finite K V] [LieAlgebra.HasTrivialRadical K h]

/-- **Splitting of a `k`-extension by a simple non-trivial module** (the "faithful" case).

Let `W ⊆ V` be Lie submodules of a finite-dimensional `h`-module, with `h` of trivial radical
(in particular a semisimple Lie algebra), `h` acting faithfully on `W`, `W` irreducible as an
`h`-module and `V/W` a trivial `h`-module. Then `W` has an `h`-submodule complement in `V`.

The complement is the kernel of the Casimir operator of the trace form of `W`: its restriction to
`W` has trace `dim h ≠ 0`, hence is non-zero, hence an isomorphism (Schur). -/
theorem exists_isCompl_of_faithful (W : LieSubmodule K h V) [LieModule.IsIrreducible K h W]
    [LieModule.IsFaithful K h W] (htriv : ∀ (x : h) (v : V), ⁅x, v⁆ ∈ W) :
    ∃ W' : LieSubmodule K h V, IsCompl W W' := by
  classical
  haveI : Module.Finite K W := inferInstance
  set β : LinearMap.BilinForm K h := LieModule.traceForm K h W with hβdef
  have hβsym : β.IsSymm := LinearMap.BilinForm.isSymm_iff.mpr (LieModule.traceForm_isSymm K h W)
  have hβinv : β.lieInvariant h := LieModule.traceForm_lieInvariant K h W
  have hβ : β.Nondegenerate :=
    Commons.Algebra.Lie.CartanCriterion.traceForm_nondegenerate
  -- a finite basis of `h`
  let b : Module.Basis (Fin (Module.finrank K h)) K h := Module.finBasis K h
  -- the Casimir operators on `W` and on `V`
  have hcommW : ∀ x : h, LieModule.toEnd K h W x ∘ₗ casimirOp (M := W) β hβ b
      = casimirOp (M := W) β hβ b ∘ₗ LieModule.toEnd K h W x :=
    fun x => casimirOp_comm β hβsym hβinv hβ b x
  have hcommV : ∀ x : h, LieModule.toEnd K h V x ∘ₗ casimirOp (M := V) β hβ b
      = casimirOp (M := V) β hβ b ∘ₗ LieModule.toEnd K h V x :=
    fun x => casimirOp_comm β hβsym hβinv hβ b x
  set ΩW : W →ₗ⁅K,h⁆ W :=
    { toLinearMap := casimirOp (M := W) β hβ b
      map_lie' := fun {x w} => (LinearMap.congr_fun (hcommW x) w).symm } with hΩW
  set ΩV : V →ₗ⁅K,h⁆ V :=
    { toLinearMap := casimirOp (M := V) β hβ b
      map_lie' := fun {x v} => (LinearMap.congr_fun (hcommV x) v).symm } with hΩV
  have htrW : trace K W (ΩW : W →ₗ[K] W) = (Module.finrank K h : K) := by
    have hcoe : (ΩW : W →ₗ[K] W) = casimirOp (M := W) β hβ b := rfl
    rw [hcoe]
    simpa using trace_casimirOp_traceForm (K := K) (L := h) (M := W) hβ b
  have hcard : (Module.finrank K h : K) ≠ 0 := by
    have hpos : 0 < Module.finrank K h := Module.finrank_pos_iff.mpr inferInstance
    exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
  have hne : ΩW ≠ 0 := by
    intro h0
    have hz : trace K W (ΩW : W →ₗ[K] W) = 0 := by
      rw [h0]
      exact map_zero _
    rw [htrW] at hz
    exact hcard hz
  have hkerW : ΩW.ker = ⊥ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top ΩW.ker with h | h
    · exact h
    · exfalso
      apply hne
      ext w
      have hw : w ∈ ΩW.ker := by rw [h]; trivial
      simpa using (LieModuleHom.mem_ker.mp hw)
  have hΩWinj : Function.Injective ΩW := ΩW.ker_eq_bot.mp hkerW
  have hrangeW : ΩW.range = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top ΩW.range with h | h
    · exfalso
      apply hne
      ext w
      have hw : (ΩW : W →ₗ[K] W) w ∈ ΩW.range := ⟨w, rfl⟩
      rw [h] at hw
      simpa using hw
    · exact h
  have hΩWsurj : Function.Surjective ΩW := ΩW.range_eq_top.mp hrangeW
  -- the two Casimir operators agree on `W`
  have hres : ∀ w : W, ΩV (w : V) = (ΩW w : V) := by
    intro w
    have hcoeV : (ΩV : V →ₗ[K] V) = casimirOp (M := V) β hβ b := rfl
    have hcoeW : (ΩW : W →ₗ[K] W) = casimirOp (M := W) β hβ b := rfl
    rw [show (ΩV (w : V) : V) = (ΩV : V →ₗ[K] V) (w : V) from rfl,
      show ((ΩW w : W) : V) = ((ΩW : W →ₗ[K] W) w : W) from rfl, hcoeV, hcoeW]
    exact casimirOp_coe β hβ b W w
  -- the Casimir on `V` maps `V` into `W`
  have hmem : ∀ v : V, ΩV v ∈ W := by
    intro v
    have hv : (ΩV v : V) = ∑ i, ⁅b i, ⁅β.dualBasis hβ b i, v⁆⁆ := by
      rw [show (ΩV v : V) = (ΩV : V →ₗ[K] V) v from rfl,
        show (ΩV : V →ₗ[K] V) = casimirOp (M := V) β hβ b from rfl]
      rw [casimirOp, sum_apply_lin]
      exact Finset.sum_congr rfl fun i _ => rfl
    rw [hv]
    exact Submodule.sum_mem _ fun i _ => htriv (b i) ⁅β.dualBasis hβ b i, v⁆
  refine ⟨(ΩV.ker : LieSubmodule K h V), ?_⟩
  rw [isCompl_iff]
  constructor
  · -- disjointness
    rw [disjoint_iff, eq_bot_iff]
    intro v hv
    rw [LieSubmodule.mem_bot]
    have hvW : v ∈ W := (LieSubmodule.mem_inf (N := W)
      (N' := (ΩV.ker : LieSubmodule K h V)) v).mp hv |>.1
    have hvk : ΩV v = 0 := LieModuleHom.mem_ker.mp ((LieSubmodule.mem_inf (N := W)
      (N' := (ΩV.ker : LieSubmodule K h V)) v).mp hv |>.2)
    have h3 : ΩW ⟨v, hvW⟩ = 0 := by
      apply Subtype.ext
      have h := hres ⟨v, hvW⟩
      rw [hvk] at h
      exact h.symm
    have h4 : (⟨v, hvW⟩ : W) = 0 := hΩWinj (by rw [h3, map_zero])
    exact congrArg Subtype.val h4
  · -- codisjointness
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨w, hw⟩ := hΩWsurj ⟨ΩV v, hmem v⟩
    have hvw : v - (w : V) ∈ ΩV.ker := by
      rw [LieModuleHom.mem_ker, map_sub, hres w, hw, sub_self]
    rw [LieSubmodule.mem_sup]
    exact ⟨(w : V), w.2, v - (w : V), hvw, by abel⟩

end Faithful


section SimpleCase

variable {K L V : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [Module.Finite K L] [LieAlgebra.IsKilling K L] [Module.Finite K V]

/-- A Lie submodule of an `L`-module, regarded as a Lie submodule over a Lie subalgebra `h ⊆ L`
(with the restricted action). -/
def toSubalgebraSubmodule (h : LieSubalgebra K L) (N : LieSubmodule K L V) :
    LieSubmodule K h V where
  __ := N.toSubmodule
  lie_mem := fun {x m} hm => by
    rw [LieSubalgebra.coe_bracket_of_module]
    exact N.lie_mem hm

@[simp] lemma toSubalgebraSubmodule_coe (h : LieSubalgebra K L) (N : LieSubmodule K L V) :
    (toSubalgebraSubmodule h N : Submodule K V) = N.toSubmodule := rfl

end SimpleCase

section SimpleCase2

variable {K L V : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [Module.Finite K L] [LieAlgebra.IsKilling K L] [Module.Finite K V]

/-- **The simple case** of the trivial-extension splitting: if `A ⊆ V` is irreducible with `V/A` a
trivial module, then `A` has a complement.

The proof uses the Casimir element of the trace form of `A` on a complement ideal of the kernel of
the action on `A` (so that the action becomes faithful). -/
theorem exists_isCompl_of_simple (A : LieSubmodule K L V) [LieModule.IsIrreducible K L A]
    (htriv : ∀ (x : L) (v : V), ⁅x, v⁆ ∈ A) :
    ∃ M : LieSubmodule K L V, IsCompl A M := by
  classical
  haveI hss : LieAlgebra.IsSemisimple K L := inferInstance
  by_cases htrivA : ∀ (x : L) (a : A), ⁅x, a⁆ = 0
  · -- Case: `A` is a trivial module, hence so is `V`.
    have htrivA' : ∀ (x : L) (v : V), v ∈ A → ⁅x, v⁆ = 0 := by
      intro x v hv
      have h := htrivA x ⟨v, hv⟩
      simpa [LieSubmodule.coe_bracket] using congrArg Subtype.val h
    have hVtriv : ∀ (x : L) (v : V), ⁅x, v⁆ = 0 := by
      have hker : (⊤ : LieIdeal K L) ≤ LieModule.ker K L V := by
        rw [← Commons.Algebra.Lie.Semisimple.lie_self_ideal (⊤ : LieIdeal K L)]
        rw [LieSubmodule.lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
        rintro z ⟨u, w, rfl⟩
        exact (LieModule.mem_ker K L V ⁅(u : L), (w : L)⁆).mpr fun v => by
          have key : ⁅⁅(u : L), (w : L)⁆, v⁆ = ⁅(u : L), ⁅(w : L), v⁆⁆ - ⁅(w : L), ⁅(u : L), v⁆⁆ := by
            rw [leibniz_lie]; abel
          rw [key, htrivA' (u : L) ⁅(w : L), v⁆ (htriv (w : L) v),
            htrivA' (w : L) ⁅(u : L), v⁆ (htriv (u : L) v), sub_self]
      intro x v
      exact (LieModule.mem_ker K L V x).mp (hker (LieSubmodule.mem_top x)) v
    obtain ⟨M₀, hM₀⟩ := Submodule.exists_isCompl (A : Submodule K V)
    refine ⟨⟨M₀, ?_⟩, ?_⟩
    · intro x m _
      rw [hVtriv x m]
      exact M₀.zero_mem
    · rw [← LieSubmodule.isCompl_toSubmodule]
      exact hM₀
  · -- Case: `A` is a non-trivial module.
    push_neg at htrivA
    set κ : LieIdeal K L := LieModule.ker K L A with hκdef
    have hkill : ∀ (x : L), x ∈ κ → ∀ w : V, w ∈ A → ⁅x, w⁆ = 0 := by
      intro x hx w hw
      have h := (LieModule.mem_ker K L A x).mp hx ⟨w, hw⟩
      simpa [LieSubmodule.coe_bracket] using congrArg Subtype.val h
    have hκtriv : ∀ (x : L), x ∈ κ → ∀ v : V, ⁅x, v⁆ = 0 := by
      intro x hx v
      have hspan : ⁅κ, κ⁆ ≤ LieModule.ker K L V := by
        rw [LieSubmodule.lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
        rintro z ⟨u, w, rfl⟩
        exact (LieModule.mem_ker K L V ⁅(u : L), (w : L)⁆).mpr fun v => by
          have key : ⁅⁅(u : L), (w : L)⁆, v⁆ = ⁅(u : L), ⁅(w : L), v⁆⁆ - ⁅(w : L), ⁅(u : L), v⁆⁆ := by
            rw [leibniz_lie]; abel
          rw [key, hkill (u : L) u.2 ⁅(w : L), v⁆ (htriv (w : L) v),
            hkill (w : L) w.2 ⁅(u : L), v⁆ (htriv (u : L) v), sub_self]
      rw [Commons.Algebra.Lie.Semisimple.lie_self_ideal κ] at hspan
      exact (LieModule.mem_ker K L V x).mp (hspan hx) v
    set h : LieIdeal K L := κᶜ with hhdef
    have hcompl : IsCompl κ h := by rw [hhdef]; exact isCompl_compl
    have hsup : κ ⊔ h = ⊤ := hcompl.sup_eq_top
    have hinf : κ ⊓ h = ⊥ := hcompl.inf_eq_bot
    haveI : Module.Finite K h := inferInstance
    haveI : LieAlgebra.HasTrivialRadical K h :=
      Commons.Algebra.Lie.Semisimple.hasTrivialRadical_ideal h
    haveI : Nontrivial h := by
      obtain ⟨x₀, a₀, ha₀⟩ := htrivA
      have hne : h ≠ ⊥ := by
        intro hbot
        have hκtop : κ = ⊤ := by
          have h1 : (⊤ : LieIdeal K L) = κ ⊔ h := hsup.symm
          rw [hbot, sup_bot_eq] at h1
          exact h1.symm
        refine ha₀ ?_
        have hx : x₀ ∈ κ := by rw [hκtop]; trivial
        exact (LieModule.mem_ker K L A x₀).mp hx a₀
      have hex : ∃ x : L, x ∈ h ∧ x ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hne (le_antisymm (fun x hx => by
          rw [LieSubmodule.mem_bot]; exact hc x hx) bot_le)
      obtain ⟨y, hy, hy0⟩ := hex
      exact ⟨⟨0, h.zero_mem⟩, ⟨y, hy⟩,
        fun hcontra => hy0 (by simpa using (congrArg Subtype.val hcontra).symm)⟩
    haveI : LieModule.IsFaithful K h A := by
      rw [LieModule.isFaithful_iff_ker_eq_bot, eq_bot_iff]
      intro x hx
      rw [LieSubmodule.mem_bot]
      have hxκ : (x : L) ∈ κ := by
        rw [LieModule.mem_ker]
        intro a
        have h := (LieModule.mem_ker K h A x).mp hx a
        simpa only [LieIdeal.coe_bracket_of_module] using h
      have hmem : (x : L) ∈ κ ⊓ h := ⟨hxκ, x.2⟩
      rw [hinf] at hmem
      exact Subtype.ext ((LieSubmodule.mem_bot (x : L)).mp hmem)
    -- The trace form of the `h`-module `A` and the associated Casimir operators.
    haveI : Module.Finite K A := inferInstance
    set β : LinearMap.BilinForm K h := LieModule.traceForm K h A with hβdef
    have hβsym : β.IsSymm := LinearMap.BilinForm.isSymm_iff.mpr (LieModule.traceForm_isSymm K h A)
    have hβinv : β.lieInvariant h := LieModule.traceForm_lieInvariant K h A
    have hβ : β.Nondegenerate :=
      Commons.Algebra.Lie.CartanCriterion.traceForm_nondegenerate
    let b : Module.Basis (Fin (Module.finrank K h)) K h := Module.finBasis K h
    -- `L`-equivariance of the two Casimir operators
    have hbh : ∀ (y : h), LieModule.toEnd K h A y = LieModule.toEnd K L A (y : L) := by
      intro y
      ext m
      rw [LieModule.toEnd_apply_apply, LieModule.toEnd_apply_apply,
        LieIdeal.coe_bracket_of_module]
    have hVh : ∀ (y : h), LieModule.toEnd K h V y = LieModule.toEnd K L V (y : L) := by
      intro y
      ext m
      rw [LieModule.toEnd_apply_apply, LieModule.toEnd_apply_apply,
        LieIdeal.coe_bracket_of_module]
    have hLeqA : ∀ x : L, LieModule.toEnd K L A x ∘ₗ casimirOp (M := A) β hβ b
        = casimirOp (M := A) β hβ b ∘ₗ LieModule.toEnd K L A x := by
      intro x
      have hxmem : x ∈ (κ : LieSubmodule K L L) ⊔ (h : LieSubmodule K L L) := by
        rw [hsup]; trivial
      obtain ⟨a, ha, c, hc, rfl⟩ := (LieSubmodule.mem_sup (κ : LieSubmodule K L L)
        (h : LieSubmodule K L L) x).mp hxmem
      have ha0 : LieModule.toEnd K L A a = 0 := by
        ext m
        exact congrArg Subtype.val ((LieModule.mem_ker K L A a).mp ha m)
      rw [show LieModule.toEnd K L A (a + c)
          = LieModule.toEnd K L A a + LieModule.toEnd K L A c from map_add _ _ _,
        LinearMap.add_comp, LinearMap.comp_add, ha0, LinearMap.zero_comp,
        LinearMap.comp_zero, zero_add, zero_add]
      have hc' := casimirOp_comm (L := h) (M := A) β hβsym hβinv hβ b ⟨c, hc⟩
      rwa [hbh ⟨c, hc⟩] at hc'
    have hLeqV : ∀ x : L, LieModule.toEnd K L V x ∘ₗ casimirOp (M := V) β hβ b
        = casimirOp (M := V) β hβ b ∘ₗ LieModule.toEnd K L V x := by
      intro x
      have hxmem : x ∈ (κ : LieSubmodule K L L) ⊔ (h : LieSubmodule K L L) := by
        rw [hsup]; trivial
      obtain ⟨a, ha, c, hc, rfl⟩ := (LieSubmodule.mem_sup (κ : LieSubmodule K L L)
        (h : LieSubmodule K L L) x).mp hxmem
      have ha0 : LieModule.toEnd K L V a = 0 := by
        ext m
        exact hκtriv a ha m
      rw [show LieModule.toEnd K L V (a + c)
          = LieModule.toEnd K L V a + LieModule.toEnd K L V c from map_add _ _ _,
        LinearMap.add_comp, LinearMap.comp_add, ha0, LinearMap.zero_comp,
        LinearMap.comp_zero, zero_add, zero_add]
      have hc' := casimirOp_comm (L := h) (M := V) β hβsym hβinv hβ b ⟨c, hc⟩
      rwa [hVh ⟨c, hc⟩] at hc'
    set ΩA : A →ₗ⁅K,L⁆ A :=
      { toLinearMap := casimirOp (M := A) β hβ b
        map_lie' := fun {x a} => (LinearMap.congr_fun (hLeqA x) a).symm } with hΩA
    set ΩV : V →ₗ⁅K,L⁆ V :=
      { toLinearMap := casimirOp (M := V) β hβ b
        map_lie' := fun {x v} => (LinearMap.congr_fun (hLeqV x) v).symm } with hΩV
    have htrA : trace K A (ΩA : A →ₗ[K] A) = (Module.finrank K h : K) := by
      have hcoe : (ΩA : A →ₗ[K] A) = casimirOp (M := A) β hβ b := rfl
      rw [hcoe]
      simpa using trace_casimirOp_traceForm (K := K) (L := h) (M := A) hβ b
    have hcard : (Module.finrank K h : K) ≠ 0 := by
      have hpos : 0 < Module.finrank K h := Module.finrank_pos_iff.mpr inferInstance
      exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
    have hneA : ΩA ≠ 0 := by
      intro h0
      have hz : trace K A (ΩA : A →ₗ[K] A) = 0 := by
        rw [h0]
        exact map_zero _
      rw [htrA] at hz
      exact hcard hz
    have hkerA : ΩA.ker = ⊥ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top ΩA.ker with h | h
      · exact h
      · exfalso
        apply hneA
        ext a
        have ha : a ∈ ΩA.ker := by rw [h]; trivial
        simpa using (LieModuleHom.mem_ker.mp ha)
    have hrangeA : ΩA.range = ⊤ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top ΩA.range with h | h
      · exfalso
        apply hneA
        ext a
        have ha : (ΩA : A →ₗ[K] A) a ∈ ΩA.range := ⟨a, rfl⟩
        rw [h] at ha
        simpa using ha
      · exact h
    have hinjA : Function.Injective ΩA := ΩA.ker_eq_bot.mp hkerA
    have hsurjA : Function.Surjective ΩA := ΩA.range_eq_top.mp hrangeA
    have hres : ∀ a : A, ΩV (a : V) = (ΩA a : V) := by
      intro a
      show (casimirOp (M := V) β hβ b) (a : V) = ((casimirOp (M := A) β hβ b) a : V)
      simp only [casimirOp]
      simp
    have hmem : ∀ v : V, ΩV v ∈ A := by
      intro v
      have hv : (ΩV v : V) = ∑ i, ⁅b i, ⁅β.dualBasis hβ b i, v⁆⁆ := by
        rw [show (ΩV v : V) = (ΩV : V →ₗ[K] V) v from rfl,
          show (ΩV : V →ₗ[K] V) = casimirOp (M := V) β hβ b from rfl]
        rw [casimirOp, sum_apply_lin]
        exact Finset.sum_congr rfl fun i _ => rfl
      rw [hv]
      exact Submodule.sum_mem _ fun i _ => htriv (b i) ⁅β.dualBasis hβ b i, v⁆
    refine ⟨(ΩV.ker : LieSubmodule K L V), ?_⟩
    rw [isCompl_iff]
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro v hv
      rw [LieSubmodule.mem_bot]
      have hvA : v ∈ A := (LieSubmodule.mem_inf (N := A)
        (N' := (ΩV.ker : LieSubmodule K L V)) v).mp hv |>.1
      have hvk : ΩV v = 0 := LieModuleHom.mem_ker.mp ((LieSubmodule.mem_inf (N := A)
        (N' := (ΩV.ker : LieSubmodule K L V)) v).mp hv |>.2)
      have h3 : ΩA ⟨v, hvA⟩ = 0 := by
        apply Subtype.ext
        have h := hres ⟨v, hvA⟩
        rw [hvk] at h
        exact h.symm
      have h4 : (⟨v, hvA⟩ : A) = 0 := hinjA (by rw [h3, map_zero])
      exact congrArg Subtype.val h4
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      obtain ⟨w, hw⟩ := hsurjA ⟨ΩV v, hmem v⟩
      have hvw : v - (w : V) ∈ ΩV.ker := by
        rw [LieModuleHom.mem_ker, map_sub, hres w, hw, sub_self]
      rw [LieSubmodule.mem_sup]
      exact ⟨(w : V), w.2, v - (w : V), hvw, by abel⟩

end SimpleCase2

section Assembly

universe u

variable {K : Type*} {L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- **Assembly step**: if every Lie submodule `W` of a finite-dimensional `L`-module with *trivial
quotient* (`[L, V] ⊆ W`) admits a Lie-submodule complement, then so does every Lie submodule.

The complement of `N` is the kernel of an `L`-equivariant linear map `T : M →ₗ N` which is the
identity on `N`.  Such a map is obtained by splitting the trivial extension
`0 → {f : M →ₗ N | f|_N = 0} → {f : M →ₗ N | f|_N ∈ K·1} → k·1 → 0` inside `Hom(M, N)`. -/
theorem exists_isCompl_of_triv_splits
    (hsplit : ∀ (V : Type u) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
      [Module.Finite K V] (W : LieSubmodule K L V), (∀ (x : L) (v : V), ⁅x, v⁆ ∈ W) →
      ∃ W' : LieSubmodule K L V, IsCompl W W')
    (M : Type u) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (N : LieSubmodule K L M) : ∃ N' : LieSubmodule K L M, IsCompl N N' := by
  classical
  rcases eq_or_ne N ⊥ with hN | hN
  · exact ⟨⊤, by rw [hN]; exact isCompl_bot_top⟩
  rcases eq_or_ne N ⊤ with hNtop | hNtop
  · exact ⟨⊥, by rw [hNtop]; exact isCompl_top_bot⟩
  haveI hNnt : Nontrivial ↥N := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact hN (by
      rw [eq_bot_iff]
      intro m hm
      rw [LieSubmodule.mem_bot]
      have hmem := Subsingleton.elim (α := ↥N) (⟨m, hm⟩ : ↥N) 0
      simpa using congrArg Subtype.val hmem)
  -- the identity endomorphism of `↥N` is non-zero
  have h10 : (1 : ↥N →ₗ[K] ↥N) ≠ 0 := by
    intro hzero
    obtain ⟨n, hn⟩ := exists_ne (0 : ↥N)
    have h' : (1 : ↥N →ₗ[K] ↥N) n = (0 : ↥N →ₗ[K] ↥N) n :=
      congrArg (fun f : ↥N →ₗ[K] ↥N => f n) hzero
    exact hn (by simpa using h')
  -- the restriction map `Hom(M, N) → End(N)`
  let ρ : (M →ₗ[K] ↥N) →ₗ⁅K,L⁆ (↥N →ₗ[K] ↥N) :=
    { toFun := fun f => f.comp N.subtype
      map_add' := by intro f g; ext n; rfl
      map_smul' := by intro a f; ext n; rfl
      map_lie' := by intro x f; ext n; rfl }
  -- the span of the identity inside `End(N)` is a trivial submodule
  let Z : LieSubmodule K L (↥N →ₗ[K] ↥N) :=
    { (K ∙ (1 : ↥N →ₗ[K] ↥N) : Submodule K (↥N →ₗ[K] ↥N)) with
      lie_mem := by
        intro x c hc
        have hc' : c ∈ (K ∙ (1 : ↥N →ₗ[K] ↥N)) := hc
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hc'
        rw [← ha, lie_smul]
        have h1 : ⁅x, (1 : ↥N →ₗ[K] ↥N)⁆ = 0 := by ext n; simp
        rw [h1, smul_zero]
        exact Submodule.zero_mem _ }
  let Q : LieSubmodule K L (M →ₗ[K] ↥N) := Z.comap ρ
  have hQmem : ∀ (f : M →ₗ[K] ↥N), f ∈ Q ↔ ρ f ∈ (K ∙ (1 : ↥N →ₗ[K] ↥N)) := by
    intro f
    rw [LieSubmodule.mem_comap]
    rfl
  have hQtriv : ∀ (x : L) (q : ↥Q), ⁅x, q⁆ ∈ (ρ.ker.comap Q.incl : LieSubmodule K L ↥Q) := by
    intro x q
    rw [LieSubmodule.mem_comap, LieModuleHom.mem_ker]
    change ρ ⁅x, (q : ↥Q)⁆ = 0
    rw [LieModuleHom.map_lie]
    have h2 := (hQmem (q : M →ₗ[K] ↥N)).mp q.2
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h2
    rw [← ha, lie_smul]
    have h3 : ⁅x, (1 : ↥N →ₗ[K] ↥N)⁆ = 0 := by ext n; simp
    rw [h3, smul_zero]
  -- the projection onto `N` along a linear complement, an element of `Q`
  obtain ⟨N₀, hN₀⟩ := Submodule.exists_isCompl (N : Submodule K M)
  let proj : M →ₗ[K] ↥N := (N : Submodule K M).projectionOnto N₀ hN₀
  have hprojρ : ρ proj = 1 := by
    apply LinearMap.ext
    intro n
    exact Submodule.projectionOnto_apply_left hN₀ n
  have hprojQ : proj ∈ Q := by
    rw [hQmem, hprojρ]
    exact Submodule.subset_span (Set.mem_singleton _)
  have hQne : (ρ.ker.comap Q.incl : LieSubmodule K L ↥Q) ≠ ⊤ := by
    intro hcon
    have hmem : (⟨proj, hprojQ⟩ : ↥Q) ∈ (ρ.ker.comap Q.incl : LieSubmodule K L ↥Q) := by
      rw [hcon]; trivial
    rw [LieSubmodule.mem_comap, LieModuleHom.mem_ker] at hmem
    change ρ proj = 0 at hmem
    rw [hprojρ] at hmem
    exact h10 hmem
  -- split the trivial extension `ker ρ ⊆ Q`
  obtain ⟨M', hM'⟩ := hsplit ↥Q (ρ.ker.comap Q.incl) hQtriv
  have hM'ne : M' ≠ ⊥ := by
    intro hcon
    exact hQne (by rw [← hM'.sup_eq_top, hcon, sup_bot_eq])
  obtain ⟨f, hfM', hfne⟩ : ∃ f : ↥Q, f ∈ M' ∧ f ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hM'ne (by
      rw [eq_bot_iff]
      intro q hq
      rw [LieSubmodule.mem_bot]
      exact hc q hq)
  have hfZ : ρ (f : M →ₗ[K] ↥N) ∈ (K ∙ (1 : ↥N →ₗ[K] ↥N)) := (hQmem _).mp f.2
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hfZ
  have ha0 : a ≠ 0 := by
    intro h0
    apply hfne
    have hker : f ∈ (ρ.ker.comap Q.incl : LieSubmodule K L ↥Q) := by
      rw [LieSubmodule.mem_comap, LieModuleHom.mem_ker]
      change ρ (f : M →ₗ[K] ↥N) = 0
      rw [← ha, h0, zero_smul]
    have hmem : f ∈ (ρ.ker.comap Q.incl : LieSubmodule K L ↥Q) ⊓ M' :=
      (LieSubmodule.mem_inf (ρ.ker.comap Q.incl) M' f).mpr ⟨hker, hfM'⟩
    rw [hM'.inf_eq_bot] at hmem
    simpa using hmem
  -- normalize `f` so that its restriction to `N` is the identity
  set T : ↥Q := a⁻¹ • f with hTdef
  have hTM' : T ∈ M' := M'.smul_mem a⁻¹ hfM'
  have hTρ : ρ ((T : ↥Q) : M →ₗ[K] ↥N) = 1 := by
    rw [hTdef]
    change ρ (a⁻¹ • (f : M →ₗ[K] ↥N)) = 1
    rw [map_smul, ← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  have hTinv : ∀ x : L, ⁅x, ((T : ↥Q) : M →ₗ[K] ↥N)⁆ = 0 := by
    intro x
    have h1 : ⁅x, T⁆ ∈ M' := M'.lie_mem hTM'
    have h3 : ρ (Q.incl ⁅x, T⁆) = 0 := by
      have hTρ' : ρ (Q.incl T) = 1 := hTρ
      rw [LieModuleHom.map_lie Q.incl, LieModuleHom.map_lie ρ, hTρ']
      ext n; simp
    have h4 : (⁅x, T⁆ : ↥Q) ∈ (ρ.ker.comap Q.incl : LieSubmodule K L ↥Q) := by
      rw [LieSubmodule.mem_comap, LieModuleHom.mem_ker]
      exact h3
    have h5 : (⁅x, T⁆ : ↥Q) ∈ (ρ.ker.comap Q.incl : LieSubmodule K L ↥Q) ⊓ M' :=
      (LieSubmodule.mem_inf (ρ.ker.comap Q.incl) M' (⁅x, T⁆)).mpr ⟨h4, h1⟩
    rw [hM'.inf_eq_bot] at h5
    have hzero : (⁅x, T⁆ : ↥Q) = 0 := by simpa using h5
    change ((⁅x, T⁆ : ↥Q) : M →ₗ[K] ↥N) = 0
    rw [hzero]
    rfl
  -- hence `T` is equivariant
  have heq : ∀ (x : L) (m : M),
      ((T : ↥Q) : M →ₗ[K] ↥N) ⁅x, m⁆ = ⁅x, ((T : ↥Q) : M →ₗ[K] ↥N) m⁆ := by
    intro x m
    have h := congrArg (fun g : M →ₗ[K] ↥N => g m) (hTinv x)
    rw [LieHom.lie_apply, LinearMap.zero_apply] at h
    exact (sub_eq_zero.mp h).symm
  have hfix : ∀ n : ↥N, ((T : ↥Q) : M →ₗ[K] ↥N) (n : M) = n := by
    intro n
    have h := congrArg (fun g : ↥N →ₗ[K] ↥N => g n) hTρ
    exact h
  -- the complement is the kernel of `T`
  let K' : LieSubmodule K L M :=
    { (LinearMap.ker ((T : ↥Q) : M →ₗ[K] ↥N) : Submodule K M) with
      lie_mem := by
        intro x m hm
        change m ∈ (LinearMap.ker ((T : ↥Q) : M →ₗ[K] ↥N) : Submodule K M) at hm
        rw [LinearMap.mem_ker] at hm
        change ⁅x, m⁆ ∈ (LinearMap.ker ((T : ↥Q) : M →ₗ[K] ↥N) : Submodule K M)
        rw [LinearMap.mem_ker, heq x m, hm, lie_zero] }
  have hinf : N ⊓ K' = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [LieSubmodule.mem_bot]
    rw [LieSubmodule.mem_inf N K' m] at hm
    obtain ⟨hmN, hmK⟩ := hm
    change m ∈ (LinearMap.ker ((T : ↥Q) : M →ₗ[K] ↥N) : Submodule K M) at hmK
    rw [LinearMap.mem_ker] at hmK
    have h2 : (⟨m, hmN⟩ : ↥N) = 0 := by
      rw [← hfix ⟨m, hmN⟩, hmK]
    exact congrArg Subtype.val h2
  have hsup : N ⊔ K' = ⊤ := by
    rw [eq_top_iff]
    intro m _
    rw [LieSubmodule.mem_sup N K' m]
    refine ⟨(((T : ↥Q) : M →ₗ[K] ↥N) m : M), (((T : ↥Q) : M →ₗ[K] ↥N) m).2,
      m - (((T : ↥Q) : M →ₗ[K] ↥N) m : M), ?_, by abel⟩
    change m - (((T : ↥Q) : M →ₗ[K] ↥N) m : M)
      ∈ (LinearMap.ker ((T : ↥Q) : M →ₗ[K] ↥N) : Submodule K M)
    rw [LinearMap.mem_ker, map_sub, hfix (((T : ↥Q) : M →ₗ[K] ↥N) m), sub_self]
  exact ⟨K', isCompl_iff.mpr ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩⟩

end Assembly

section Main

/-- **Weyl's complete reducibility theorem** (characteristic zero form): every Lie submodule of a
finite-dimensional module over a Lie algebra with non-degenerate Killing form has a Lie-submodule
complement.

If `L` is a subsingleton then any linear complement works.  Otherwise `LieAlgebra.IsKilling K L`
makes `L` finite-dimensional and semisimple; then the trivial-extension splitting
(`exists_isCompl_of_triv_quotient_univ`, whose irreducible case is handled by the Casimir element
of the trace form, `exists_isCompl_of_simple`) combines with the assembly step
`exists_isCompl_of_triv_splits` to produce a complement for an arbitrary submodule. -/
theorem isCompl_of_isKilling {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [LieAlgebra.IsKilling K L] [Module.Finite K M]
    (N : LieSubmodule K L M) : ∃ N' : LieSubmodule K L M, IsCompl N N' := by
  classical
  by_cases hL : Nontrivial L
  · haveI : Module.Finite K L := Commons.Algebra.Lie.Killing.moduleFinite
    refine exists_isCompl_of_triv_splits ?_ M N
    intro V _ _ _ _ _ W h
    exact Commons.Algebra.Lie.CompleteReducibility.exists_isCompl_of_triv_quotient_univ
      (fun V' _ _ _ _ _ A hA htriv => by
        haveI : LieModule.IsIrreducible K L A := hA
        exact exists_isCompl_of_simple A htriv) V W h
  · haveI : Subsingleton L := not_nontrivial_iff_subsingleton.mp hL
    obtain ⟨N₀, hN₀⟩ := Submodule.exists_isCompl (N : Submodule K M)
    refine ⟨⟨N₀, ?_⟩, ?_⟩
    · intro x m _
      rw [Subsingleton.elim x 0, zero_lie]
      exact N₀.zero_mem
    · rw [← LieSubmodule.isCompl_toSubmodule]
      exact hN₀

end Main

end Commons.Algebra.Lie.CompleteReducibility
