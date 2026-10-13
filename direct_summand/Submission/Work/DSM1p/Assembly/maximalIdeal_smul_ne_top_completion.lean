import Mathlib
import Submission.Work.DSM1p.Basic
import Submission.Work.DSM1p.Root.stepMap_alg

/-!
# Faithfulness of the `p`-adic completion of the root closure

Let `R` be a commutative local ring whose maximal ideal `𝔪 ∋ p` contains the prime `p`, and let
`a ∈ 𝔪`.  This file proves that the maximal ideal does not act surjectively on the `p`-adic
completion of the root closure `R[a^{1/p^∞}]`:

`𝔪 • ⊤ ≠ ⊤` in `Submodule R (RootClosureCompletion R p a)`.

This is the faithfulness hypothesis of Bhatt's flatness criterion (arXiv:1608.08882, Prop. 4.1),
consumed by `Work.DSM1p.Assembly.faithfullyFlat_of_flat_of_maximalIdeal_smul_ne_top`, and it is
the `p`-adic-completion analogue of the statement for the (uncompleted) root closure
`Work.DSM1p.RootClosure`.

## The argument

Since `𝔪 ⊇ (p)`, a linear map `ψ` out of the completion that kills `(p)` and whose values in the
residue field `R ⧸ 𝔪` are `R`-linear automatically satisfies `𝔪 • ⊤ ≤ ker ψ` (the elements of `𝔪`
act by `0` on `R ⧸ 𝔪`).  To conclude it suffices to produce a *surjective* unital `ψ`, because
then `ψ 1 = 1 ≠ 0` while every element of `𝔪 • ⊤` maps to `0`.

Such a `ψ` is assembled from the level-`1` projection of the adic completion,
`AdicCompletion.evalOneₐ : RootClosureCompletion R p a → R[a^{1/p^∞}] ⧸ (p)`
(`Submission.Work.DSM1p.Completion.mod_p`), and a surjective ring hom

`φ : R[a^{1/p^∞}] →+* R ⧸ 𝔪`

constructed in `exists_surjective_residue_map`: because `a ∈ 𝔪`, the image of `a` in `R ⧸ 𝔪` is
`0`, so the `p^n`-th root `x` of `a` may legitimately be sent to `0`; the induced maps on the
stages `R[x]/(x^{p^n} - a) → R ⧸ 𝔪`, `x ↦ 0`, are compatible with the transition maps `x ↦ x^p`
of the tower (`RootTower.stepMap_algebraMap`, `RootTower.stepMap_root`) and therefore descend to
the filtered colimit by `Ring.DirectLimit.lift`.
-/

namespace Work.DSM1p.Assembly

open Work.DSM1p

/-- **A surjective residue map on the root closure.**  If `a ∈ 𝔪` for an ideal `𝔪` of `R` and
`0 < p`, the ring `R[a^{1/p^∞}]` admits a surjective ring homomorphism to `R ⧸ 𝔪` that extends
the quotient map `R → R ⧸ 𝔪` and kills the adjoined `p`-power roots of `a` (which it may, since
`a` itself maps to `0`). -/
theorem exists_surjective_residue_map (R : Type*) [CommRing R] (m : Ideal R) (p : ℕ)
    (hp : 0 < p) (a : R) (ha : a ∈ m) :
    ∃ φ : RootClosure R p a →+* (R ⧸ m), Function.Surjective φ ∧
      ∀ r : R, φ (algebraMap R (RootClosure R p a) r) = Ideal.Quotient.mk m r := by
  -- The defining relation `X ^ p^n - C a` vanishes at `0` over `R ⧸ m`, because `a ↦ 0`.
  have hrel : ∀ n : ℕ, Polynomial.eval₂ (Ideal.Quotient.mk m) (0 : R ⧸ m)
      (Polynomial.X ^ (p ^ n) - Polynomial.C a : Polynomial R) = 0 := by
    intro n
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    rw [zero_pow (pow_ne_zero n hp.ne'), sub_zero]
  -- The `n`-th stage map `R[x]/(x^{p^n} - a) → R ⧸ m`, `x ↦ 0`.
  let f : (n : ℕ) → RootTower R p a n →+* (R ⧸ m) :=
    fun n => AdjoinRoot.lift (Ideal.Quotient.mk m) 0 (hrel n)
  -- The stage maps are compatible with the transition maps of the tower.
  have hf : ∀ (i j : ℕ) (hij : i ≤ j) (x : RootTower R p a i),
      f j (RootTower.stepMap R p a i j hij x) = f i x := by
    intro i j hij x
    have hcomp : (f j).comp (RootTower.stepMap R p a i j hij) = f i := by
      apply AdjoinRoot.ringHom_ext
      · -- agreement on the base ring
        ext r
        simp only [RingHom.comp_apply]
        rw [← AdjoinRoot.algebraMap_eq (Polynomial.X ^ p ^ i - Polynomial.C a)]
        rw [Work.DSM1p.Root.stepMap_algebraMap]
        rw [AdjoinRoot.algebraMap_eq (Polynomial.X ^ p ^ j - Polynomial.C a)]
        rw [AdjoinRoot.lift_of]
        rw [AdjoinRoot.algebraMap_eq (Polynomial.X ^ p ^ i - Polynomial.C a), AdjoinRoot.lift_of]
      · -- agreement on the adjoined root (both sides are `0`)
        simp only [RingHom.comp_apply]
        rw [Work.DSM1p.Root.stepMap_root, map_pow, AdjoinRoot.lift_root,
            zero_pow (pow_ne_zero (j - i) hp.ne'), AdjoinRoot.lift_root]
    exact congrFun (congrArg DFunLike.coe hcomp) x
  refine ⟨Ring.DirectLimit.lift (RootTower R p a)
      (fun i j h => ⇑(RootTower.stepMap R p a i j h)) (R ⧸ m) f hf, ?_, ?_⟩
  · -- surjectivity: the stage-`0` map already induces the surjection `R → R ⧸ m`
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := m) y
    refine ⟨algebraMap R (RootClosure R p a) r, ?_⟩
    rw [show algebraMap R (RootClosure R p a) r
        = RootClosure.of R p a 0 (AdjoinRoot.of (Polynomial.X ^ p ^ 0 - Polynomial.C a) r) from rfl]
    rw [Ring.DirectLimit.lift_of, AdjoinRoot.lift_of]
  · -- it extends the quotient map `R → R ⧸ m`
    intro r
    rw [show algebraMap R (RootClosure R p a) r
        = RootClosure.of R p a 0 (AdjoinRoot.of (Polynomial.X ^ p ^ 0 - Polynomial.C a) r) from rfl]
    rw [Ring.DirectLimit.lift_of, AdjoinRoot.lift_of]

/-- **The maximal ideal does not act surjectively on the `p`-adic completion of the root
closure.**  For a local ring `R` with `p ∈ 𝔪` and `a ∈ 𝔪`, the completion
`(R[a^{1/p^∞}])^` is not annihilated — as a module — by `𝔪`: `𝔪 • ⊤ ≠ ⊤`. -/
theorem maximalIdeal_smul_ne_top_completion (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ)
    (hp : 0 < p) (hR : (p : R) ∈ IsLocalRing.maximalIdeal R) (a : R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) :
    IsLocalRing.maximalIdeal R •
      (⊤ : Submodule R (Work.DSM1p.RootClosureCompletion R p a)) ≠ ⊤ := by
  set m := IsLocalRing.maximalIdeal R with hm
  have hmne : m ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  -- suppose `𝔪` acts surjectively
  intro htop
  obtain ⟨φ, hφsurj, hφmap⟩ := exists_surjective_residue_map R m p hp a ha
  set I : Ideal (RootClosure R p a) := Ideal.span {(p : RootClosure R p a)} with hI
  -- `φ` kills `(p)` because `p ∈ 𝔪`
  have hker : I ≤ RingHom.ker φ := by
    rw [hI, Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    show φ (p : RootClosure R p a) = 0
    rw [show (p : RootClosure R p a) = algebraMap R (RootClosure R p a) p from
      (map_natCast _ p).symm, hφmap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hR
  -- descent of `φ` to `R[a^{1/p^∞}] ⧸ (p)`
  set φbar : RootClosure R p a ⧸ I →+* (R ⧸ m) :=
    Ideal.Quotient.lift I φ (fun x hx => RingHom.mem_ker.mp (hker hx)) with hφbardef
  have hφbarmk : ∀ x : RootClosure R p a, φbar (Ideal.Quotient.mk I x) = φ x := by
    intro x
    rw [hφbardef]
    exact Ideal.Quotient.lift_mk I φ _ (a := x)
  -- compose with the level-`1` projection of the `p`-adic completion
  set ψ : RootClosureCompletion R p a →+* (R ⧸ m) :=
    φbar.comp (AdicCompletion.evalOneₐ I).toRingHom with hψdef
  -- `ψ` agrees with `φ` on the image of the root closure
  have psi_alg : ∀ s : RootClosure R p a,
      ψ (algebraMap (RootClosure R p a) (RootClosureCompletion R p a) s) = φ s := by
    intro s
    have h1 : (AdicCompletion.evalOneₐ I) (algebraMap (RootClosure R p a)
        (AdicCompletion I (RootClosure R p a)) s) = Ideal.Quotient.mk I s :=
      congrFun (congrArg DFunLike.coe (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk I)) s
    calc ψ (algebraMap (RootClosure R p a) (RootClosureCompletion R p a) s)
        = φbar ((AdicCompletion.evalOneₐ I)
            (algebraMap (RootClosure R p a) (RootClosureCompletion R p a) s)) := rfl
      _ = φbar ((AdicCompletion.evalOneₐ I)
            (algebraMap (RootClosure R p a) (AdicCompletion I (RootClosure R p a)) s)) := rfl
      _ = φbar (Ideal.Quotient.mk I s) := by rw [h1]
      _ = φ s := hφbarmk s
  -- `ψ` is unital and surjective
  have psi_one : ψ 1 = 1 := by
    calc ψ 1 = φbar ((AdicCompletion.evalOneₐ I) 1) := rfl
      _ = φbar 1 := by rw [map_one]
      _ = φbar (Ideal.Quotient.mk I (1 : RootClosure R p a)) := by
            rw [map_one (Ideal.Quotient.mk I)]
      _ = φ (1 : RootClosure R p a) := hφbarmk 1
      _ = 1 := map_one φ
  have psi_surj : Function.Surjective ψ := by
    intro y
    obtain ⟨s, rfl⟩ := hφsurj y
    obtain ⟨x, hx⟩ := AdicCompletion.evalOneₐ_surjective I (Ideal.Quotient.mk I s)
    refine ⟨x, ?_⟩
    calc ψ x = φbar ((AdicCompletion.evalOneₐ I) x) := rfl
      _ = φbar (Ideal.Quotient.mk I s) := by rw [hx]
      _ = φ s := hφbarmk s
  -- crucially, `ψ` vanishes on `𝔪 • ⊤`, since `𝔪` acts as `0` on `R ⧸ 𝔪`
  have hzero : ∀ x ∈ m • (⊤ : Submodule R (RootClosureCompletion R p a)), ψ x = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr n _
      rw [show r • n = algebraMap R (RootClosureCompletion R p a) r * n from Algebra.smul_def r n,
        map_mul]
      have hz : ψ (algebraMap R (RootClosureCompletion R p a) r) = 0 := by
        rw [show algebraMap R (RootClosureCompletion R p a) r
            = algebraMap (RootClosure R p a) (RootClosureCompletion R p a)
                (algebraMap R (RootClosure R p a) r) from rfl]
        rw [psi_alg, hφmap]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
      rw [hz, zero_mul]
    · intro x y hx hy
      rw [map_add, hx, hy, zero_add]
  -- but `1` is not killed, since `ψ 1 = 1 ≠ 0`
  have h1 : ψ 1 = 0 := hzero 1 (by rw [htop]; exact Submodule.mem_top)
  rw [psi_one] at h1
  have : Nontrivial (R ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hmne
  exact one_ne_zero h1

end Work.DSM1p.Assembly
