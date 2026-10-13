import Mathlib
import Submission.Work.DSM1p.Family
import Submission.Work.DSM1p.Family.flat_closure

/-!
# Injectivity of the transition maps of the multi-parameter root tower

Let `R` be a commutative ring, `p` a natural number and `x : Fin d → R`.  The `n`-th stage of the
multi-parameter root tower is

`FamTower R p x n = R[Z₁,…,Z_d] ⧸ (Z_i ^ (p ^ n) - x_i)`,

with `Z_i` the `p ^ n`-th root of `x_i`, and the transition maps
`FamTower.stepMap R p x m n h : FamTower R p x m →+* FamTower R p x n` for `m ≤ n` send the
`m`-th root of `x_i` to the `p ^ (n - m)`-th power of the `n`-th root of `x_i`.

The present lemma is that these transition maps are **injective**.

## The argument

`flat_closure` provides, for every `N ≠ 0`, the normal form of the quotient of
`R[Z]` by the relations `Z_i ^ N - x_i`: the classes of the monomials whose exponent is `< N` in
every variable form an `R`-basis, realized by the explicit `R`-linear bijection

`stageMap N x : (RedIdx d N →₀ R) ≃ₗ[R] R[Z] ⧸ (Z_i ^ N - x_i)`.

The single transition map `FamTower.step R p x n` is computed on this basis: writing `expand p`
for the substitution `Z_i ↦ Z_i ^ p` of `MvPolynomial`,

* `step (stageMk (p ^ n) x q) = stageMk (p ^ (n+1)) x (expand p q)` (`step_stageMk`), and hence
* `step (stageMap (p ^ n) x l) = stageMap (p ^ (n+1)) x (embDomain (stepIdx p n _) l)`
  (`step_stageMap`),

where `stepIdx p n hp : RedIdx d (p ^ n) ↪ RedIdx d (p ^ (n+1))` multiplies an exponent vector by
`p` (`p * a_i < p ^ (n+1)` because `a_i < p ^ n`).  Since `stageMap` is injective on both sides
and `Finsupp.embDomain` of an injective map is injective, `step` is injective.  A composite of
injective maps is injective, so every iterate `stepIter` is injective; finally `stepMap` is
`stepIter` transported along the (definitional) equality `m + (n - m) = n`, and transporting an
injective function along an equality of its target type preserves injectivity.
-/

namespace Work.DSM1p.Family

variable {R : Type*} [CommRing R] {d : ℕ}

/-! ## The exponent scaling of a single step -/

/-- The scaling of a reduced multi-index by `p`, from level `n` to level `n + 1`: the exponent
`a_i < p ^ n` becomes `p * a_i < p ^ (n + 1)`. -/
noncomputable def stepIdx (p n : ℕ) (hp : 0 < p) : RedIdx d (p ^ n) → RedIdx d (p ^ (n + 1)) :=
  fun a => ⟨p • a.1, fun i => by
    rw [Finsupp.smul_apply, smul_eq_mul]
    calc p * a.1 i < p * p ^ n := Nat.mul_lt_mul_of_pos_left (a.2 i) hp
      _ = p ^ (n + 1) := (pow_succ' p n).symm⟩

lemma stepIdx_injective (p n : ℕ) (hp : 0 < p) : Function.Injective (stepIdx (d := d) p n hp) := by
  intro a b hab
  have h : p • a.1 = p • b.1 := congrArg Subtype.val hab
  refine Subtype.ext (Finsupp.ext fun i => ?_)
  have hi : p * (a.1 i) = p * (b.1 i) := by
    have := congrArg (fun f : Fin d →₀ ℕ => f i) h
    simpa only [Finsupp.smul_apply, smul_eq_mul] using this
  exact Nat.mul_left_cancel hp hi

/-! ## The transition map on the quotient of `MvPolynomial` -/

/-- The algebra map `R[Z] → FamTower R p x (n+1)` sending `Z_i` to the `(n+1)`-st root is the
quotient map onto the `(n+1)`-st stage. -/
lemma eval₂Hom_algebraMap_root_eq_stageMk (p n : ℕ) (x : Fin d → R) :
    MvPolynomial.eval₂Hom (algebraMap R (FamTower R p x (n + 1)))
        (fun i => FamTower.root R p x (n + 1) i)
      = stageMk (p ^ (n + 1)) x := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [MvPolynomial.eval₂Hom_C]
    rfl
  · intro i
    rw [MvPolynomial.eval₂Hom_X']

/-- The transition map `FamTower.step R p x n` is the substitution `Z_i ↦ Z_i ^ p` followed by the
quotient map onto the `(n+1)`-st stage. -/
lemma step_stageMk (p n : ℕ) (x : Fin d → R) (q : MvPolynomial (Fin d) R) :
    FamTower.step R p x n (stageMk (p ^ n) x q) =
      stageMk (p ^ (n + 1)) x (MvPolynomial.expand p q) := by
  rw [FamTower.step, Ideal.Quotient.lift_mk]
  change MvPolynomial.eval₂Hom (algebraMap R (FamTower R p x (n + 1)))
      ((fun i => FamTower.root R p x (n + 1) i) ^ p) q =
    stageMk (p ^ (n + 1)) x (MvPolynomial.expand p q)
  rw [← MvPolynomial.eval₂Hom_comp_expand (p := p)
      (f := algebraMap R (FamTower R p x (n + 1)))
      (g := fun i => FamTower.root R p x (n + 1) i)]
  rw [RingHom.comp_apply, eval₂Hom_algebraMap_root_eq_stageMk]
  rfl

/-! ## The transition map on the normal-form coordinates -/

/-- On the normal-form coordinates `(RedIdx d (p ^ n) →₀ R)`, the transition map `FamTower.step`
is the exponent scaling `stepIdx`. -/
lemma step_stageMap (p n : ℕ) (hp : 0 < p) (x : Fin d → R) (l : RedIdx d (p ^ n) →₀ R) :
    FamTower.step R p x n (stageMap (p ^ n) x l) =
      stageMap (p ^ (n + 1)) x
        (Finsupp.embDomain ⟨stepIdx p n hp, stepIdx_injective p n hp⟩ l) := by
  refine Finsupp.induction_linear l ?h0 ?hadd ?hsingle
  · simp
  · intro f g hf hg
    rw [map_add, map_add, hf, hg, Finsupp.embDomain_add, map_add]
  · intro a c
    rw [stageMap_apply, phi_single, step_stageMk, MvPolynomial.expand_monomial,
      Finsupp.embDomain_single, stageMap_apply, phi_single]
    simp only [Function.Embedding.coeFn_mk, stepIdx, Subtype.coe_mk]

/-! ## Injectivity of `stageMap` (the normal-form coordinates of a stage) -/

/-- The normal-form coordinates of a stage are injective. -/
lemma stageMap_bijective_injective (N : ℕ) (hN : N ≠ 0) (x : Fin d → R) :
    Function.Injective (stageMap N x) := by
  have hker : ∀ l : RedIdx d N →₀ R, stageMap N x l = 0 → l = 0 := by
    intro l hl
    have h1 : phi N l ∈ stageIdeal N x :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [stageMap_apply] using hl)
    have h2 : red N x hN (phi N l) = 0 := red_mem_stageIdeal N x hN h1
    have h3 : phi N l = 0 := by rw [← red_phi N x hN l, h2]
    exact phi_injective N (by rw [h3, map_zero])
  intro l l' hll
  have h : l - l' = 0 := by
    refine hker (l - l') ?_
    rw [map_sub, hll, sub_self]
  rwa [sub_eq_zero] at h

/-- The normal-form coordinates of a stage are surjective (they exhaust the quotient). -/
lemma stageMap_bijective_surjective (N : ℕ) (hN : N ≠ 0) (x : Fin d → R) :
    Function.Surjective (stageMap N x) := by
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨redShift N x hN ((AddMonoidAlgebra.coeffLinearEquiv R) p), ?_⟩
  show stageMk N x (red N x hN p) = stageMk N x p
  exact (mk_red N x hN p).symm

/-! ## Injectivity of the transition maps -/

/-- A single transition map `FamTower.step R p x n` is injective. -/
lemma step_injective (p n : ℕ) (hp : 0 < p) (x : Fin d → R) :
    Function.Injective (FamTower.step R p x n) := by
  intro y z hyz
  obtain ⟨l, hl⟩ := stageMap_bijective_surjective (d := d) (p ^ n) (pow_ne_zero n hp.ne') x y
  obtain ⟨l', hl'⟩ := stageMap_bijective_surjective (d := d) (p ^ n) (pow_ne_zero n hp.ne') x z
  have h2 : l = l' := by
    apply Finsupp.embDomain_injective ⟨stepIdx p n hp, stepIdx_injective p n hp⟩
    apply stageMap_bijective_injective (d := d) (p ^ (n + 1)) (pow_ne_zero (n + 1) hp.ne') x
    rw [← step_stageMap p n hp x l, ← step_stageMap p n hp x l', hl, hl']
    exact hyz
  rw [← hl, ← hl', h2]

/-- A composite of transition maps is injective. -/
lemma stepIter_injective (p : ℕ) (hp : 0 < p) (x : Fin d → R) (m : ℕ) :
    ∀ k, Function.Injective (FamTower.stepIter R p x m k) := by
  intro k
  induction k with
  | zero =>
    rw [show FamTower.stepIter R p x m 0 = RingHom.id _ from rfl]
    exact Function.injective_id
  | succ k ih =>
    rw [show FamTower.stepIter R p x m (k + 1) =
        (FamTower.step R p x (m + k)).comp (FamTower.stepIter R p x m k) from rfl]
    rw [RingHom.coe_comp]
    exact (step_injective p (m + k) hp x).comp ih

/-- Transporting an injective map along an equality of its target type (here: of the index of a
stage of the tower) preserves injectivity. -/
lemma famTower_index_cast_injective (p : ℕ) (x : Fin d → R) {m i j : ℕ} (e : i = j)
    (f : FamTower R p x m →+* FamTower R p x i) (hf : Function.Injective f) :
    Function.Injective (e ▸ f) := by
  cases e
  exact hf

theorem stepMap_injective (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] {d : ℕ} (x : Fin d → R)
    {m n : ℕ} (h : m ≤ n) :
    Function.Injective (Work.DSM1p.FamTower.stepMap R p x m n h) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [show FamTower.stepMap R p x m n h =
      (Nat.add_sub_cancel' h ▸ FamTower.stepIter R p x m (n - m)) from rfl]
  exact famTower_index_cast_injective p x (Nat.add_sub_cancel' h)
    (FamTower.stepIter R p x m (n - m)) (stepIter_injective p hp x m (n - m))

end Work.DSM1p.Family
