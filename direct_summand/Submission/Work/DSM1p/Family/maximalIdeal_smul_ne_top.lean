import Mathlib
import Submission.Work.DSM1p.Family
import Submission.Work.DSM1p.Family.stepMap_algebraMap
import Submission.Work.DSM1p.Family.stepMap_root

/-!
# `𝔪 • ⊤ ≠ ⊤` for the multi-parameter cover `R[x₁^{1/p^∞}, …, x_d^{1/p^∞}]^{^}`

Let `R` be a local ring with `p ∈ 𝔪 = IsLocalRing.maximalIdeal R` and let `x : Fin d → R` be a
family of elements of `𝔪`.  We prove that the maximal ideal does not act surjectively on the
`p`-adic completion `A′ = Work.DSM1p.FamCompletion R p x` of the root closure
`A = R[x₁^{1/p^∞}, …, x_d^{1/p^∞}]`:

`𝔪 • (⊤ : Submodule R A′) ≠ ⊤`.

This is the faithfulness hypothesis of Bhatt's flatness criterion (arXiv:1608.08882, Prop. 4.1)
for the `d`-parameter (regular system of parameters) cover, and it is the multi-parameter
analogue of `Work.DSM1p.Assembly.maximalIdeal_smul_ne_top_completion`.

## The argument

Since `x_i ∈ 𝔪`, the residue map `R → R ⧸ 𝔪` kills every `x_i`; hence the `n`-th stage
`R[Z]/(Z_i^{p^n} - x_i)` admits a ring homomorphism to `R ⧸ 𝔪` sending each variable `Z_i ↦ 0`
(`stageRed`).  These are compatible with the transition maps of the tower (`stageRed_compat`),
so they descend to a ring hom `φ : A = R[x₁^{1/p^∞}, …, x_d^{1/p^∞}] →+* R ⧸ 𝔪` extending
`R → R ⧸ 𝔪` (`redHom`).  Since also `p ∈ 𝔪`, the map `φ` kills `(p) ⊆ A`, so it descends to
`A ⧸ (p)`, and composing with the level-`1` projection of the `p`-adic completion
(`AdicCompletion.evalOneₐ`) gives a *unital* ring homomorphism

`ψ : A′ →+* R ⧸ 𝔪`

which kills `𝔪 • ⊤` (the elements of `𝔪` act by `0` on the residue field) but satisfies
`ψ 1 = 1 ≠ 0`.  Hence `1 ∉ 𝔪 • ⊤`, i.e. `𝔪 • ⊤ ≠ ⊤`.
-/

namespace Work.DSM1p.Family

open MvPolynomial

/-! ## The reduction of a stage modulo the maximal ideal -/

/-- **The reduction map of the `n`-th stage.**  Since `x i ∈ 𝔪`, the defining relation
`Z_i ^ (p ^ n) = x_i` of the stage `R[Z]/(Z_i ^ (p ^ n) - x_i)` maps to `0 ^ (p ^ n) = 0` under
the "all variables ↦ 0" evaluation into `R ⧸ 𝔪`, so it descends to the quotient. -/
noncomputable def stageRed (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (𝔪 : Ideal R)
    (hx : ∀ i, x i ∈ 𝔪) (hp0 : 0 < p) (n : ℕ) : FamTower R p x n →+* R ⧸ 𝔪 :=
  Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom (Ideal.Quotient.mk 𝔪) (fun _ : Fin d => (0 : R ⧸ 𝔪)))
    (fun a ha => by
      refine RingHom.mem_ker.mp ?_
      exact Ideal.span_le.mpr (by
        rintro g ⟨i, rfl⟩
        refine RingHom.mem_ker.mpr ?_
        rw [map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
        rw [zero_pow (pow_ne_zero n hp0.ne'), Ideal.Quotient.eq_zero_iff_mem.mpr (hx i),
          sub_zero]) ha)

/-- The reduction map computed on a polynomial representative. -/
lemma stageRed_mk (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (𝔪 : Ideal R)
    (hx : ∀ i, x i ∈ 𝔪) (hp0 : 0 < p) (n : ℕ) (q : MvPolynomial (Fin d) R) :
    stageRed R p x 𝔪 hx hp0 n (Ideal.Quotient.mk _ q) =
      MvPolynomial.eval₂Hom (Ideal.Quotient.mk 𝔪) (fun _ : Fin d => (0 : R ⧸ 𝔪)) q :=
  Ideal.Quotient.lift_mk _ _ _

/-- The reduction map extends the quotient map `R → R ⧸ 𝔪`. -/
lemma stageRed_of (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (𝔪 : Ideal R)
    (hx : ∀ i, x i ∈ 𝔪) (hp0 : 0 < p) (n : ℕ) (r : R) :
    stageRed R p x 𝔪 hx hp0 n (algebraMap R (FamTower R p x n) r) = Ideal.Quotient.mk 𝔪 r := by
  rw [show algebraMap R (FamTower R p x n) r = Ideal.Quotient.mk _ (MvPolynomial.C r) from rfl]
  rw [stageRed_mk]
  exact MvPolynomial.eval₂Hom_C _ _ r

/-- The reduction map kills the adjoined roots. -/
lemma stageRed_root (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (𝔪 : Ideal R)
    (hx : ∀ i, x i ∈ 𝔪) (hp0 : 0 < p) (n : ℕ) (i : Fin d) :
    stageRed R p x 𝔪 hx hp0 n (FamTower.root R p x n i) = 0 := by
  rw [show FamTower.root R p x n i = Ideal.Quotient.mk _ (MvPolynomial.X i) from rfl]
  rw [stageRed_mk]
  exact MvPolynomial.eval₂Hom_X' _ _ i

/-- The reduction maps of the stages are compatible with the transition maps of the tower. -/
lemma stageRed_compat (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (𝔪 : Ideal R)
    (hx : ∀ i, x i ∈ 𝔪) (hp0 : 0 < p) (m n : ℕ) (h : m ≤ n) :
    (stageRed R p x 𝔪 hx hp0 n).comp (FamTower.stepMap R p x m n h) =
      stageRed R p x 𝔪 hx hp0 m := by
  refine Ideal.Quotient.ringHom_ext ?_
  refine MvPolynomial.ringHom_ext ?_ ?_
  · intro r
    simp only [RingHom.comp_apply]
    rw [show (Ideal.Quotient.mk _ (MvPolynomial.C r) : FamTower R p x m) =
        algebraMap R (FamTower R p x m) r from rfl]
    rw [stepMap_algebraMap, stageRed_of, stageRed_of]
  · intro i
    simp only [RingHom.comp_apply]
    rw [show (Ideal.Quotient.mk _ (MvPolynomial.X i) : FamTower R p x m) =
        FamTower.root R p x m i from rfl]
    rw [stepMap_root, map_pow, stageRed_root, stageRed_root,
      zero_pow (pow_ne_zero (n - m) hp0.ne')]

/-! ## The reduction map of the root closure -/

/-- **The reduction map of the root closure.**  The compatible family of reductions of the
stages descends to the filtered colimit `A = R[x₁^{1/p^∞}, …, x_d^{1/p^∞}]`. -/
noncomputable def redHom (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (𝔪 : Ideal R)
    (hx : ∀ i, x i ∈ 𝔪) (hp0 : 0 < p) : FamClosure R p x →+* R ⧸ 𝔪 :=
  Ring.DirectLimit.lift (FamTower R p x) (fun m n h => ⇑(FamTower.stepMap R p x m n h))
    (R ⧸ 𝔪) (stageRed R p x 𝔪 hx hp0)
    (fun m n h y => congrFun (congrArg DFunLike.coe (stageRed_compat R p x 𝔪 hx hp0 m n h)) y)

/-- The reduction map computed on an element of a stage. -/
lemma redHom_of (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (𝔪 : Ideal R)
    (hx : ∀ i, x i ∈ 𝔪) (hp0 : 0 < p) (n : ℕ) (y : FamTower R p x n) :
    redHom R p x 𝔪 hx hp0 (FamClosure.of R p x n y) = stageRed R p x 𝔪 hx hp0 n y :=
  Ring.DirectLimit.lift_of (R ⧸ 𝔪) _ _ n y

/-- The reduction map extends the quotient map `R → R ⧸ 𝔪`. -/
lemma redHom_algebraMap (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (𝔪 : Ideal R)
    (hx : ∀ i, x i ∈ 𝔪) (hp0 : 0 < p) (r : R) :
    redHom R p x 𝔪 hx hp0 (algebraMap R (FamClosure R p x) r) = Ideal.Quotient.mk 𝔪 r := by
  have h : algebraMap R (FamClosure R p x) r =
      FamClosure.of R p x 0 (algebraMap R (FamTower R p x 0) r) := rfl
  rw [h, redHom_of, stageRed_of]

/-- The reduction map is unital. -/
lemma redHom_one (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (𝔪 : Ideal R)
    (hx : ∀ i, x i ∈ 𝔪) (hp0 : 0 < p) :
    redHom R p x 𝔪 hx hp0 1 = 1 := by
  have h : (1 : FamClosure R p x) = FamClosure.of R p x 0 1 :=
    ((FamClosure.of R p x 0).map_one).symm
  rw [h, redHom_of, map_one]

/-! ## The main theorem -/

theorem maximalIdeal_smul_ne_top (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ) (hp0 : 0 < p)
    (hpm : (p : R) ∈ IsLocalRing.maximalIdeal R) {d : ℕ} (x : Fin d → R)
    (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R) :
    IsLocalRing.maximalIdeal R •
      (⊤ : Submodule R (Work.DSM1p.FamCompletion R p x)) ≠ ⊤ := by
  set m := IsLocalRing.maximalIdeal R with hm
  set φ := redHom R p x m hx hp0 with hφdef
  intro htop
  -- `φ` kills `(p)`, because `p ∈ 𝔪`
  have hφp : φ (p : FamClosure R p x) = 0 := by
    rw [show (p : FamClosure R p x) = algebraMap R (FamClosure R p x) p from
      (map_natCast _ p).symm]
    rw [hφdef, redHom_algebraMap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpm
  -- descent of `φ` to `A ⧸ (p)`
  set I : Ideal (FamClosure R p x) := Ideal.span {(p : FamClosure R p x)} with hI
  have hker : ∀ a ∈ I, φ a = 0 := by
    intro a ha
    rw [hI] at ha
    have hle : Ideal.span {(p : FamClosure R p x)} ≤ RingHom.ker φ :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (RingHom.mem_ker.mpr hφp))
    exact RingHom.mem_ker.mp (hle ha)
  set φbar : FamClosure R p x ⧸ I →+* (R ⧸ m) :=
    Ideal.Quotient.lift I φ hker with hφbardef
  have hφbarmk : ∀ s : FamClosure R p x, φbar (Ideal.Quotient.mk I s) = φ s := by
    intro s
    rw [hφbardef]
    exact Ideal.Quotient.lift_mk I φ _ (a := s)
  -- compose with the level-`1` projection of the `p`-adic completion
  set ψ : FamCompletion R p x →+* (R ⧸ m) :=
    φbar.comp (AdicCompletion.evalOneₐ I).toRingHom with hψdef
  have psi_one : ψ 1 = 1 := by
    calc ψ 1 = φbar ((AdicCompletion.evalOneₐ I) 1) := rfl
      _ = φbar 1 := by rw [map_one]
      _ = φbar (Ideal.Quotient.mk I (1 : FamClosure R p x)) := by
            rw [map_one (Ideal.Quotient.mk I)]
      _ = φ (1 : FamClosure R p x) := hφbarmk 1
      _ = 1 := by rw [hφdef, redHom_one]
  -- `ψ` agrees with `φ` on the image of the root closure
  have psi_alg : ∀ s : FamClosure R p x,
      ψ (algebraMap (FamClosure R p x) (FamCompletion R p x) s) = φ s := by
    intro s
    have h1 : (AdicCompletion.evalOneₐ I) (algebraMap (FamClosure R p x)
        (AdicCompletion I (FamClosure R p x)) s) = Ideal.Quotient.mk I s :=
      congrFun (congrArg DFunLike.coe (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk I)) s
    calc ψ (algebraMap (FamClosure R p x) (FamCompletion R p x) s)
        = φbar ((AdicCompletion.evalOneₐ I)
            (algebraMap (FamClosure R p x) (FamCompletion R p x) s)) := rfl
      _ = φbar ((AdicCompletion.evalOneₐ I)
            (algebraMap (FamClosure R p x) (AdicCompletion I (FamClosure R p x)) s)) := rfl
      _ = φbar (Ideal.Quotient.mk I s) := by rw [h1]
      _ = φ s := hφbarmk s
  -- crucially, `ψ` vanishes on `𝔪 • ⊤`
  have hzero : ∀ y ∈ m • (⊤ : Submodule R (FamCompletion R p x)), ψ y = 0 := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr n _
      rw [show r • n = algebraMap R (FamCompletion R p x) r * n from Algebra.smul_def r n,
        map_mul]
      have hz : ψ (algebraMap R (FamCompletion R p x) r) = 0 := by
        rw [show algebraMap R (FamCompletion R p x) r
            = algebraMap (FamClosure R p x) (FamCompletion R p x)
                (algebraMap R (FamClosure R p x) r) from rfl]
        rw [psi_alg, hφdef, redHom_algebraMap]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
      rw [hz, zero_mul]
    · intro a b ha hb
      rw [map_add, ha, hb, zero_add]
  -- but `1` is not killed
  have hmem : (1 : FamCompletion R p x) ∈ m • (⊤ : Submodule R (FamCompletion R p x)) := by
    rw [htop]
    exact Submodule.mem_top
  have h1 : ψ 1 = 0 := hzero 1 hmem
  rw [psi_one] at h1
  have : Nontrivial (R ⧸ m) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  exact one_ne_zero h1

end Work.DSM1p.Family
