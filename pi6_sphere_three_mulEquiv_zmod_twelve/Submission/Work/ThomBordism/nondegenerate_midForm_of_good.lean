import Mathlib
import Submission.Work.Cohomology.pd_middleDegree_of_good
import Submission.Work.ThomBordism.evaluation_kernel_torsion_of_pd
import Submission.Work.Cohomology.kronH_capPair_cup
import Submission.Work.Bordism.Middle

set_option synthInstance.maxHeartbeats 400000

/-!
# Nondegeneracy of the middle intersection form of a `Good` manifold

Let `M` be a closed topological `2n`-manifold (`n` even) with a fundamental class
`c ∈ H_{2n}(M;ℤ)` satisfying the `Good` predicate of `Work.Cohomology.pd_good` — i.e. Poincaré–Lefschetz
duality holds for `M` at the class `c`, which by `Work.Cohomology.pd_middleDegree_of_good` gives the
bijectivity of the middle cap product `y ↦ y ⌢ c : Hⁿ(M;ℤ) → Hₙ(M;ℤ)`.

The main result of this file is that the rationalised middle intersection form
`midForm (k := n) ⟨M, c⟩` (`y ↦ ⟨y ⌣ y, c⟩` on `Hⁿ(M;ℤ) ⊗[ℤ] ℚ`) is **nondegenerate**.

## Strategy

Everything is reduced to the integral picture, where only three facts are used:

* **symmetry** of the intersection *pairing* `⟨y ⌣ z, c⟩` in the middle degree of a `4k`-manifold
  (for `n` even, `(-1)^{n·n} = 1`): `Work.ThomBordism.interForm_symm_of_even`;
* the **radical is torsion**: if `⟨y ⌣ z, c⟩ = 0` for all `z` then `y` is a torsion class
  (`Work.ThomBordism.mem_torsion_of_forall_interForm_eq_zero`, from the cap-product bijectivity and
  `Work.ThomBordism.evaluation_kernel_torsion_of_pd`);
* the **algebra** of base change along `ℤ → ℚ`: a symmetric integral form whose radical consists of
  torsion is nondegenerate after `⊗[ℤ] ℚ` (`Work.ThomBordism.nondegenerate_baseChangeBilin`).

The last item is proved by "clearing denominators": every `x ∈ ℚ ⊗[ℤ] M` has a non-zero multiple
`N • x = 1 ⊗ m` with `m ∈ M`
(`Work.ThomBordism.exists_nat_smul_tmul_one_aux`), while torsion elements die in the tensor product
(`Work.ThomBordism.tmul_one_eq_zero_of_mem_torsion'`).
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open TensorProduct

namespace Work.ThomBordism

noncomputable section

/-! ## Tensor algebra: clearing denominators in `ℚ ⊗[ℤ] M` -/

/-- A `ℚ`-scalar acts on a pure tensor by multiplication on the first factor. -/
private lemma rat_smul_tmul' {M : Type*} [AddCommGroup M] [Module ℤ M] (q a : ℚ) (m : M) :
    q • (a ⊗ₜ[ℤ] m) = (q * a) ⊗ₜ[ℤ] m := by
  rw [TensorProduct.tmul_eq_smul_one_tmul (R := ℤ) a m, smul_smul,
    TensorProduct.tmul_eq_smul_one_tmul (R := ℤ) (q * a) m]

attribute [local instance 100] ZSMul.toSMul in
/-- **Integral scalars can be moved across the tensor product**: for `c : ℤ` and `m : M` the two
expressions `1 ⊗ (c • m)` and `c • (1 ⊗ m)` in `ℚ ⊗[ℤ] M` agree.  This is the basic balanced-tensor
relation `(c • 1) ⊗ m = 1 ⊗ (c • m)`; it is the only place where the compatibility of the `ℤ`-action
with the tensor product is used. -/
private lemma tmul_one_smul {M : Type*} [AddCommGroup M] [Module ℤ M] (c : ℤ) (m : M) :
    (1 : ℚ) ⊗ₜ[ℤ] (c • m) = c • ((1 : ℚ) ⊗ₜ[ℤ] m) := by
  have h : (TensorProduct.mk ℤ ℚ M (1 : ℚ)) (c • m)
      = c • ((TensorProduct.mk ℤ ℚ M (1 : ℚ)) m) := LinearMap.map_smul _ c m
  rwa [TensorProduct.mk_apply, TensorProduct.mk_apply] at h

/-- `den * a = num` for a rational number `a`. -/
private lemma rat_den_mul (a : ℚ) : (a.den : ℚ) * a = (a.num : ℚ) := by
  have h : (a.num : ℚ) = a * (a.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast a.den_nz : (a.den : ℚ) ≠ 0)).mp (Rat.num_div_den a)
  rw [h, mul_comm]

attribute [local instance 100] ZSMul.toSMul in
/-- A natural number acting on `1 ⊗ m` moves to the second factor. -/
private lemma nat_smul_tmul_one {M : Type*} [AddCommGroup M] [Module ℤ M] (k : ℕ) (m : M) :
    (k : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] m) = (1 : ℚ) ⊗ₜ[ℤ] (k • m) := by
  rw [show (k : ℚ) = ((k : ℤ) : ℚ) from by norm_num, Int.cast_smul_eq_zsmul,
    ← tmul_one_smul, Nat.cast_smul_eq_nsmul]

attribute [local instance 100] ZSMul.toSMul in
/-- **Clearing denominators.**  Every element of `ℚ ⊗[ℤ] M` has a non-zero natural multiple of the
form `1 ⊗ m`.  (A general element is a finite sum `Σ qᵢ ⊗ mᵢ`; multiplying by a common denominator
makes the coefficients integral, and the integral coefficients can be moved to the second factor by
`tmul_one_smul`.) -/
private lemma exists_nat_smul_tmul_one_aux {M : Type*} [AddCommGroup M] [Module ℤ M]
    (x : TensorProduct ℤ ℚ M) :
    ∃ N : ℕ, N ≠ 0 ∧ ∃ m : M, (N : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] m := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul a m =>
      rcases eq_or_ne a 0 with rfl | ha
      · exact ⟨1, one_ne_zero, 0, by simp⟩
      · refine ⟨a.den, a.den_nz, (a.num : ℤ) • m, ?_⟩
        rw [rat_smul_tmul', rat_den_mul]
        rw [show (a.num : ℚ) = (a.num : ℤ) • (1 : ℚ) from
          (Int.smul_one_eq_cast (R := ℚ) a.num).symm]
        rw [← TensorProduct.smul_tmul']
        exact (tmul_one_smul (a.num : ℤ) m).symm
  | add x y hx hy =>
      obtain ⟨N₁, hN₁, m₁, hm₁⟩ := hx
      obtain ⟨N₂, hN₂, m₂, hm₂⟩ := hy
      refine ⟨N₁ * N₂, Nat.mul_ne_zero hN₁ hN₂, N₂ • m₁ + N₁ • m₂, ?_⟩
      rw [Nat.cast_mul]
      have step1 : ((N₁ : ℚ) * (N₂ : ℚ)) • (x + y)
          = (N₂ : ℚ) • ((N₁ : ℚ) • x) + (N₁ : ℚ) • ((N₂ : ℚ) • y) := by
        rw [mul_smul, smul_add, smul_add, smul_comm (N₁ : ℚ) (N₂ : ℚ) x]
      rw [step1, hm₁, hm₂, nat_smul_tmul_one, nat_smul_tmul_one, ← TensorProduct.tmul_add]

attribute [local instance 100] ZSMul.toSMul in
/-- **Torsion dies in `ℚ ⊗[ℤ] M`.** -/
private lemma tmul_one_eq_zero_of_mem_torsion' {M : Type*} [AddCommGroup M] [Module ℤ M] {m : M}
    (hm : m ∈ Submodule.torsion ℤ M) : (1 : ℚ) ⊗ₜ[ℤ] m = 0 := by
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (M := M) m).mp hm
  have hane : (a : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero a
  have hq : ((a : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hane
  have ha' : (a : ℤ) • m = 0 := Submonoid.smul_def a m ▸ ha
  have h1 : (a : ℤ) • ((1 : ℚ) ⊗ₜ[ℤ] m) = 0 := by
    rw [← tmul_one_smul, ha', TensorProduct.tmul_zero]
  have h2 : ((a : ℤ) : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] m) = 0 := by
    rw [Int.cast_smul_eq_zsmul, h1]
  calc (1 : ℚ) ⊗ₜ[ℤ] m
      = (((a : ℤ) : ℚ)⁻¹ * ((a : ℤ) : ℚ)) • ((1 : ℚ) ⊗ₜ[ℤ] m) := by
        rw [inv_mul_cancel₀ hq, one_smul]
    _ = ((a : ℤ) : ℚ)⁻¹ • (((a : ℤ) : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] m)) := by rw [mul_smul]
    _ = 0 := by rw [h2, smul_zero]

/-- From `⅟2 • W = 0` in `ℚ` conclude `W = 0`. -/
private lemma invOf_two_smul_eq_zero {W : ℚ} (h : (⅟(2:ℚ)) • W = 0) : W = 0 := by
  have h2 : (2 : ℚ) • ((⅟(2 : ℚ)) • W) = (2 : ℚ) • (0 : ℚ) := by rw [h]
  rwa [smul_smul, mul_invOf_self, one_smul, smul_zero] at h2

/-! ## The base change of a symmetric integral form with torsion radical -/

attribute [local instance 100] ZSMul.toSMul in
/-- **Base change to `ℚ` of a symmetric integral form whose radical is torsion is nondegenerate.**

If `B` is a symmetric `ℤ`-bilinear form on `M` such that every `m` with `B m · = 0` is a torsion
element, then the induced `ℚ`-bilinear form `baseChangeBilin B` on `ℚ ⊗[ℤ] M` has trivial radical,
i.e. the quadratic form `x ↦ B̃ x x` is nondegenerate.

Indeed, if the polar form of `x ↦ B̃ x x` vanishes, then (by symmetry) `B̃ x y = 0` for all `y`;
clearing denominators, `N • x = 1 ⊗ m`, and evaluating on `1 ⊗ z` shows `B m z = 0` for all `z`, so
`m` is torsion, so `1 ⊗ m = 0`, so `x = 0`. -/
theorem nondegenerate_baseChangeBilin {M : Type*} [AddCommGroup M] [Module ℤ M]
    (B : M →ₗ[ℤ] M →ₗ[ℤ] ℤ) (hsym : ∀ m n, B m n = B n m)
    (htor : ∀ m, (∀ n, B m n = 0) → m ∈ Submodule.torsion ℤ M) :
    Work.Bordism.Nondegenerate
      (Work.SignatureBordism.quadOfBilin (Work.SignatureBordism.baseChangeBilin B)) := by
  intro x hx
  -- symmetry of the rationalised form
  have hBsym : ∀ u v : TensorProduct ℤ ℚ M,
      (Work.SignatureBordism.baseChangeBilin B) u v
        = (Work.SignatureBordism.baseChangeBilin B) v u := by
    have hflip : (Work.SignatureBordism.baseChangeBilin B)
        = (Work.SignatureBordism.baseChangeBilin B).flip := by
      apply Work.SignatureBordism.tensor_bilin_ext
      intro a b m n
      rw [LinearMap.flip_apply, Work.SignatureBordism.baseChangeBilin_tmul,
        Work.SignatureBordism.baseChangeBilin_tmul, hsym m n]
      ring
    intro u v
    conv_lhs => rw [hflip]
    exact LinearMap.flip_apply (Work.SignatureBordism.baseChangeBilin B) v u
  -- the polar form vanishing forces `B̃ x y = 0` for all `y`
  have hzero : ∀ y, (Work.SignatureBordism.baseChangeBilin B) x y = 0 := by
    intro y
    have hW : (Work.SignatureBordism.quadOfBilin (Work.SignatureBordism.baseChangeBilin B)) (x + y)
        - (Work.SignatureBordism.quadOfBilin (Work.SignatureBordism.baseChangeBilin B)) x
        - (Work.SignatureBordism.quadOfBilin (Work.SignatureBordism.baseChangeBilin B)) y = 0 := by
      have h := hx y
      rw [QuadraticMap.associated_apply] at h
      exact invOf_two_smul_eq_zero h
    simp only [Work.SignatureBordism.quadOfBilin_apply, map_add, LinearMap.add_apply] at hW
    rw [hBsym y x] at hW
    linarith
  -- clear denominators
  obtain ⟨N, hN, m₀, hm₀⟩ := exists_nat_smul_tmul_one_aux x
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have hz : ∀ z : M, B m₀ z = 0 := by
    intro z
    have h1 : (Work.SignatureBordism.baseChangeBilin B) ((1 : ℚ) ⊗ₜ[ℤ] m₀)
        ((1 : ℚ) ⊗ₜ[ℤ] z) = 0 := by
      rw [← hm₀, map_smul, LinearMap.smul_apply, hzero, smul_zero]
    rw [Work.SignatureBordism.baseChangeBilin_tmul] at h1
    norm_num at h1
    exact_mod_cast h1
  have hfin : (N : ℚ) • x = 0 := by
    rw [hm₀, tmul_one_eq_zero_of_mem_torsion' (htor m₀ hz)]
  calc x = ((N : ℚ)⁻¹ * (N : ℚ)) • x := by rw [inv_mul_cancel₀ hNq, one_smul]
    _ = (N : ℚ)⁻¹ • ((N : ℚ) • x) := by rw [mul_smul]
    _ = 0 := by rw [hfin, smul_zero]

/-- The canonical `ℤ`-action of an additive commutative group (`ZSMul.toSMul`) agrees with the one
carried by a `Module ℤ` structure on it (all such structures are propositionally equal). -/
private lemma zsmulToSMul_eq (H : Type*) [AddCommGroup H] [Module ℤ H] :
    (ZSMul.toSMul : SMul ℤ H) = (inferInstance : Module ℤ H).toDistribSMul.toSMul := by
  have h : (inferInstance : Module ℤ H) = AddCommGroup.toIntModule H := Subsingleton.elim _ _
  rw [h]
  rfl

/-! ## Symmetry of the middle intersection pairing for even degree -/

attribute [local instance 100] ZSMul.toSMul in
/-- **The middle intersection pairing is symmetric in even degree.**  For `k` even, the sign
`(-1)^{k·k}` in the graded commutativity of the cup product is `+1`, so
`⟨y ⌣ z, c⟩ = ⟨z ⌣ y, c⟩`. -/
theorem interForm_symm_of_even (X : SSet) (k : ℕ) (hk : Even k)
    (c : (Work.Cohomology.chainC ℤ X).homology (k + k))
    (y z : (Work.Cohomology.cochainC ℤ X).homology k) :
    Work.SignatureBordism.interForm ℤ X k k c y z
      = Work.SignatureBordism.interForm ℤ X k k c z y := by
  rw [Work.SignatureBordism.interForm_apply, Work.SignatureBordism.interForm_apply]
  have h := Work.Cohomology.gradedComm ℤ X k k y z
  rw [Subsingleton.elim (Nat.add_comm k k) rfl] at h
  have h' : ((Work.Cohomology.cupH' ℤ X k k) y z)
      = (-1 : ℤ) ^ (k * k) • ((Work.Cohomology.cupH' ℤ X k k) z y) := h
  have h1 : (1 : ℤ) • ((Work.Cohomology.cupH' ℤ X k k) z y)
      = ((Work.Cohomology.cupH' ℤ X k k) z y) := by
    rw [← zsmulToSMul_eq ((Work.Cohomology.cochainC ℤ X).homology (k + k))]
    exact one_zsmul _
  rw [h', Even.neg_one_pow (hk.mul_right k), h1]

/-! ## The radical of the middle intersection form is torsion -/

attribute [local instance 100] ZSMul.toSMul in
/-- **The radical of the middle intersection form consists of torsion classes.**  If the cap product
with the fundamental class `c` is bijective on the middle degree (Poincaré duality) and the homology
of `M` is degreewise finitely generated, then a class `y ∈ Hⁿ(M;ℤ)` with `⟨y ⌣ z, c⟩ = 0` for all
`z` is a torsion class.

Indeed `⟨y ⌣ z, c⟩ = (kronH z)(y ⌢ c)`, so the homology class `y ⌢ c` is annihilated by every
functional `Hₙ → ℤ` (every functional is a Kronecker pairing by
`Work.ThomBordism.kronH_surjective`), hence is torsion by
`Work.ThomBordism.mem_torsion_of_forall_apply_eq_zero`; and `y ↦ y ⌢ c` is injective. -/
theorem mem_torsion_of_forall_interForm_eq_zero {M : TopCat} (n : ℕ)
    (c : (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj M)).homology (n + n))
    (hcap : Function.Bijective
      (fun y : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj M)).homology n =>
        (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj M) n n) y c))
    (hfg : ∀ k, Module.Finite ℤ ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj M)).homology k))
    (y : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj M)).homology n)
    (h : ∀ z : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj M)).homology n,
      Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj M) n n c y z = 0) :
    y ∈ Submodule.torsion ℤ ((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj M)).homology n) := by
  let Φ : ((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj M)).homology n) →ₗ[ℤ]
      ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj M)).homology n) :=
    (Work.ThomBordism.evalAtLM c).comp (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj M) n n)
  have hΦfun : ∀ z, Φ z = (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj M) n n) z c :=
    fun z => rfl
  have hΦ : Function.Bijective Φ := by
    change Function.Bijective (fun y => Φ y)
    rw [show (fun y => Φ y)
        = (fun y => (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj M) n n) y c)
      from funext hΦfun]
    exact hcap
  have hkron : ∀ z : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj M)).homology n,
      (Work.Cohomology.kronH ℤ (TopCat.toSSet.obj M) n z) (Φ y) = 0 := by
    intro z
    have hz := h z
    rw [Work.SignatureBordism.interForm_apply_eq_kronH_capPair] at hz
    simpa [hΦfun] using hz
  have hkill : ∀ χ : ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj M)).homology n) →ₗ[ℤ] ℤ,
      χ (Φ y) = 0 := by
    intro χ
    obtain ⟨z, hz⟩ := Work.ThomBordism.kronH_surjective (TopCat.toSSet.obj M) n
      (fun k => Work.Cohomology.singularChains_free M k) χ
    rw [← hz, hkron z]
  have htor : Φ y ∈ Submodule.torsion ℤ
      ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj M)).homology n) :=
    Work.ThomBordism.mem_torsion_of_forall_apply_eq_zero (hfg n) _ hkill
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff
    (M := (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj M)).homology n) _).mp htor
  have ha' : (a : ℤ) • Φ y = 0 := Submonoid.smul_def a (Φ y) ▸ ha
  have h2 : Φ ((a : ℤ) • y) = 0 := by rw [map_smul, ha']
  have h3 : (a : ℤ) • y = 0 := hΦ.1 (by rw [h2, map_zero])
  exact (Submodule.mem_torsion_iff
    (M := (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj M)).homology n) y).mpr
    ⟨a, Submonoid.smul_def a y ▸ h3⟩

/-! ## The main theorem -/

theorem nondegenerate_midForm_of_good {n : ℕ} {M : TopCat} [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + n))) M] (hn : Even n)
    {c : (Work.Cohomology.singularChains ℤ M).homology (n + n)}
    (hgood : Work.Cohomology.Good (n + n) c Set.univ isOpen_univ)
    (hfg : ∀ k, Module.Finite ℤ ((Work.Cohomology.singularChains ℤ M).homology k)) :
    Work.Bordism.Nondegenerate (Work.Bordism.midForm (k := n) ⟨M, c⟩) := by
  have hsym : ∀ y z : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj M)).homology n,
      Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj M) n n c y z
        = Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj M) n n c z y :=
    fun y z => interForm_symm_of_even (TopCat.toSSet.obj M) n hn c y z
  have htor : ∀ y : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj M)).homology n,
      (∀ z, Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj M) n n c y z = 0) →
      y ∈ Submodule.torsion ℤ ((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj M)).homology n) :=
    fun y h => mem_torsion_of_forall_interForm_eq_zero n c
      (Work.Cohomology.pd_middleDegree_of_good n M c hgood) (fun k => hfg k) y h
  exact nondegenerate_baseChangeBilin
    (Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj M) n n c) hsym htor

end

end Work.ThomBordism
