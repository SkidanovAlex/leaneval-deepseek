import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E5Route.pairing_formula
import Submission.Work.SSGRoute.phi0_lamV_separates
import Submission.Work.SSGRoute.phi0_pTor_scalar

/-! Guidance from the project lead (the requester):

LEAD NOTE (re-dispatch): the previous prover declared this FALSE; the designer REBUTTED it (DESIGN_FIX.md 'Addendum: E4Ω ker κ'). The statement is TRUE and UNCHANGED.
Claim (b) was right: every c-family kills ker κ_L (κ_L h = h ∪ ζ ∈ Br(L/k)).
Claim (a) is false exactly on ker κ_L: the colimit V = H²(G_k, μ_p) embeds in Br(k), and so does H²(Gal(L/k), Lˣ). So κ_L h = 0 implies h DIES at a higher level, and compatibility forces lam(h) = 0. Example: h₀ = χ∪χ over ℚ(√2) maps to (2,−1), which splits since −1 = N(1+√2); h₀ dies at ℚ(√2, i).
Every compatible family therefore kills ker κ_L. That is R1 (Work.SSGRoute.phi0_family_vanish_of_local), from compatibility and injectivity of inflation on H²(C).
ROUTE (DESIGN_FIX.md E4Ω section, R1/R2/R3): lam factors through the Brauer localisation; extend by linear algebra; read off each a_v via Br(k_v)[p] ≅ ℤ/p and E8′ (brauer_single_place, PROVED); realise with R2 (zeta_idele_class_pairing, PROVED). E2 ext_idele_shapiro is also PROVED.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 4000000

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

/-! ## The assembly of E4Ω from three arithmetic pieces (statement + plan)

`Phi0.phi0_of_pieces` is the reduction of the target to three independent arithmetic inputs, all
delegated (see the requests `SSGRoute/phi0_pairing_formula`, `SSGRoute/phi0_lamV_separates`,
`SSGRoute/phi0_pTor_scalar`, `SSGRoute/phi0_muClassHom_pairing`):

* `P2` — the **local pairing formula** (`Work.SSGRoute.phi0_pairing_formula`): the level value of
  the pairing with the `μ_p`-idèle class `c₀(f)` is the sum of the local functionals `lamV v` with
  coefficients `f v`, only finitely many of which are nonzero;
* `P3` — **separation** (`Work.SSGRoute.phi0_lamV_separates`): the local functionals `lamV v`
  separate the points of `V`;
* `P4` — **cyclicity** (`Work.SSGRoute.phi0_pTor_scalar`): every additive endomorphism of the
  `p`-torsion `A[p]` of the class-group colimit is multiplication by a natural number.

Once these three are on disk, the target follows by
`exact Phi0.phi0_of_pieces p ζ hζ (fun f x => phi0_pairing_formula p k K Ω ζ hζ f x)
(fun x hx => phi0_lamV_separates p k K Ω ζ hζ x hx) (fun φ => phi0_pTor_scalar p k K Ω φ)
lam hp hcompat`.

**Proof plan for `phi0_of_pieces`** (a draft was elaborated in this session; the pieces below are
the ones that were still failing, with the reason recorded):
1. `Λ := lamColim p lam hcompat` has `p`-torsion values: `p • Λ x = Λ (p • x) = 0`, because
   `Phi0.levelCohLimit_smul_p` (proved below) says `V` has exponent `p` (via
   `Work.SSGRoute.extH_trivial_zmodp_smul_eq_zero`, `Submission/Work/SSGRoute/phi1_level_trivial_two`).
   Likewise `p • lamV v x = 0` (`Phi0.phiColim_smul_p`, proved below).
2. `T : V →+ ⊕_v A[p]`, `T x := Finsupp.ofSupportFinite (fun v => ⟨lamV v x, ·⟩) _`, the finite
   support being the `S` of `P2` (with `f = 0`); `T` is injective by `P3` (`T (x - y) = 0` and
   `P3 (x - y)` give `x = y`).
3. Extend `Λ` along `T`: with `e : V ≃+ T.range` (`AddEquiv.ofBijective T.rangeRestrict`, using
   injectivity of `T` and `T.rangeRestrict_surjective`), apply `addHom_extend_of_exponent`
   (`Work.SSGRoute.addHom_extend_of_exponent`, exponent `p` on the free module) to
   `Λt.comp e.symm.toAddMonoidHom`; this gives `Φ : (Place k →₀ A[p]) →+ A[p]` with
   `Φ (T x) = Λt x = ⟨Λ x, ·⟩`.
4. Coefficient extraction: apply `P4` to `φ_v : A[p] →+ A[p]`, `y ↦ Φ (Finsupp.single v y)`,
   giving `n v : ℕ` with `Φ (Finsupp.single v y) = n v • y`; then
   `(Φ g : A) = g.sum (fun v y => n v • ↑y)` by `Finsupp.induction_linear` (the additivity step
   uses `Finsupp.sum_add_index` and `smul_add`; the `single` step uses
   `Finsupp.sum_single_index`, `Work.SSGRoute.pTor_coe_nsmul` and the extraction identity).
5. Evaluate at `T x`: `Λ x = Σ_{v ∈ S} n v • lamV v x` (`Finsupp.sum`, `Finset.sum_subset` against
   the support inclusion, `ZMod.val_natCast` and `nsmul_mod_eq_nsmul` below to convert `n v` into
   `((n v : ZMod p)).val`), which by `P2` for `f := fun v => (n v : ZMod p)` is
   `Φ (cOfFun f) x`; hence `Λ = Φ (cOfFun f)` (`AddMonoidHom.ext`).
6. Read the levelwise identity off the colimits: for a level `L`, `of_L (phiTriv (mk₀ c) h) =
   Φ (cOfFun f) (of_L h) = Λ (of_L h) = of_L (lam L h)` (`Phi0.phiColim_of`, `lamColim_of`), and
   `ClassLevelLimit.of_injective` finishes.

**Known pitfalls of the draft** (all in step 2–4 above, none mathematical):
* `Subtype.ext_iff.mp` on the `p`-torsion subtype needs the *value* equalities spelled out;
* the exponent-`p` fact for `↥(pTor p A)` is `(y : ↥(pTor p A)).2`, not `y.property` (type mismatch);
* plain `simp` does not see through `Phi0.lamV` (a `def` whose body is `by classical exact`):
  use `rw [Phi0.lamV]` and then the `AddMonoidHom` lemmas;
* `set_option maxHeartbeats 4000000` was not enough for the `isDefEq`/`whnf` steps involving
  `Finsupp (Place k) ↥(pTor p (ClassLevelLimit …))`; consider naming the abbreviations with
  `abbrev`/`let` and `set_option synthInstance.maxHeartbeats` or proving the linear algebra over a
  *generic* pair of exponent-`p` groups first (the Finsupp step is abstract). -/

/-- If `p • y = 0` then `n • y` only depends on `n` modulo `p`. -/
theorem nsmul_mod_eq_nsmul {M : Type*} [AddCommMonoid M] {p : ℕ} (y : M) (hp : p • y = 0)
    (n : ℕ) : (n % p) • y = n • y := by
  conv_rhs => rw [← Nat.mod_add_div n p]
  rw [add_nsmul, mul_nsmul, hp, nsmul_zero, add_zero]

theorem Phi0.torsion_extend (p : ℕ) [Fact p.Prime] {ι V B C : Type*} [AddCommGroup V]
    [AddCommGroup B] [AddCommGroup C] (hB : ∀ y : B, p • y = 0)
    (e : B →+ C) (T : V →+ (ι →₀ B)) (hT : Function.Injective T) (Λ : V →+ B)
    (hP4 : ∀ φ : B →+ B, ∃ n : ℕ, ∀ y, φ y = n • y) :
    ∃ n : ι → ℕ, ∀ x : V, e (Λ x) = (T x).sum (fun i y => n i • e y) := by
  classical
  have hF : ∀ g : ι →₀ B, p • g = 0 := fun g => by
    refine Finsupp.ext (fun i => ?_)
    rw [Finsupp.smul_apply, Finsupp.zero_apply]
    exact hB (g i)
  have hbij : Function.Bijective T.rangeRestrict :=
    ⟨fun a b h => hT (Subtype.ext_iff.mp h), T.rangeRestrict_surjective⟩
  let ee : V ≃+ T.range := AddEquiv.ofBijective T.rangeRestrict hbij
  let Λr : T.range →+ B := Λ.comp ee.symm.toAddMonoidHom
  obtain ⟨Φ, hΦ, -⟩ := addHom_extend_of_exponent p hF T.range Λr (fun w => hB (Λr w))
  have hΦT : ∀ x : V, Φ (T x) = Λ x := by
    intro x
    have h1 : Φ ((T.rangeRestrict x : T.range) : ι →₀ B) = Λr (T.rangeRestrict x) := hΦ _
    have h2 : ee.symm (T.rangeRestrict x) = x := ee.symm_apply_apply x
    have h3 : Λr (T.rangeRestrict x) = Λ x := by
      show Λ (ee.symm (T.rangeRestrict x)) = Λ x
      rw [h2]
    rw [h3] at h1
    exact h1
  have hex : ∀ i : ι, ∃ n : ℕ, ∀ y : B, Φ (Finsupp.single i y) = n • y :=
    fun i => hP4 (Φ.comp (Finsupp.singleAddHom i))
  choose n hn using hex
  refine ⟨n, fun x => ?_⟩
  have key : ∀ g : ι →₀ B, e (Φ g) = g.sum (fun i y => n i • e y) := by
    intro g
    refine Finsupp.induction_linear g ?_ ?_ ?_
    · rw [Finsupp.sum_zero_index, map_zero, map_zero]
    · intro f' g' hf hg
      rw [map_add, map_add, hf, hg]
      exact (Finsupp.sum_add_index (f := f') (g := g')
        (h := fun i y => n i • e y) (by intro a ha; simp)
        (by intro a ha b1 b2; rw [map_add, smul_add])).symm
    · intro a b
      have h1 : (Finsupp.single a b).sum (fun i y => n i • e y) = n a • e b :=
        Finsupp.sum_single_index (by simp)
      have h2 : e (Φ (Finsupp.single a b)) = n a • e b := by
        rw [hn a b, map_nsmul]
      rw [h1, h2]
  rw [← hΦT x]
  exact key (T x)

section Assembly

variable [FiniteDimensional k K] [IsGalois k K] [IsAlgClosed Ω]

open scoped BigOperators

theorem Phi0.classLevelMap_injective (L L' : Lvl k K Ω) (h : L ≤ L') :
    Function.Injective (classLevelMap (k := k) (K := K) (Ω := Ω) L L' h) := by
  intro x y hxy
  rw [classLevelMap_apply, classLevelMap_apply] at hxy
  letI : Algebra ↥L.1 ↥L'.1 := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower k ↥L.1 ↥L'.1 := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Work.SSGRoute.E4R3.inflC_injective k ↥L.1 ↥L'.1 hxy

theorem Phi0.ClassLevelLimit_of_injective (L : Lvl k K Ω) :
    Function.Injective (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L) := by
  intro x y hxy
  have hsub : ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨L', hLL', hzero⟩ :=
    (ClassLevelLimit.of_eq_zero_iff (k := k) (K := K) (Ω := Ω) L (x - y)).mp hsub
  have hzero' : classLevelMap (k := k) (K := K) (Ω := Ω) L L' hLL' (x - y) = 0 := by
    rw [classLevelMap_apply]; exact hzero
  exact sub_eq_zero.mp (Phi0.classLevelMap_injective L L' hLL' (by rw [hzero', map_zero]))

/-- **E4Ω from the three pieces** (see the plan above). -/
theorem Phi0.phi0_of_pieces (p : ℕ) [Fact p.Prime] (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (P2 : ∀ (f : NK.GlobalCFT.Place k → ZMod p)
      (x : LevelCohLimit (k := k) (K := K) (Ω := Ω) p), ∃ S : Finset (NK.GlobalCFT.Place k),
      (∀ v ∉ S, Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x = 0) ∧
      Phi0.phiColim (k := k) (K := K) (Ω := Ω) p (Phi0.cOfFun (k := k) (K := K) p ζ hζ f) x
        = ∑ v ∈ S, (f v).val • Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x)
    (P3 : ∀ x : LevelCohLimit (k := k) (K := K) (Ω := Ω) p, x ≠ 0 →
      ∃ v : NK.GlobalCFT.Place k, Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x ≠ 0)
    (P4 : ∀ φ : ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) →+
        ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))), ∃ n : ℕ, ∀ y, φ y = n • y)
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2 →+ extH (classesK k L) 2)
    (hp : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2), p • lam L h = 0)
    (hcompat : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
      (hLL : L ≤ L') (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
      inflCIn (k := k) hLL (lam L h) = lam L' (inflTrivIn (k := k) hLL (ZMod p) h)) :
    ∃ c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K,
      ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
        phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c) h = lam L h := by
  classical
  have hexS : ∀ x : LevelCohLimit (k := k) (K := K) (Ω := Ω) p,
      ∃ S : Finset (NK.GlobalCFT.Place k), ∀ v : NK.GlobalCFT.Place k,
          Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x ≠ 0 → v ∈ S := by
    intro x
    obtain ⟨S, hS, -⟩ := P2 0 x
    exact ⟨S, fun v hv => by_contra (fun h => hv (hS v h))⟩
  have hpt : ∀ (x : LevelCohLimit (k := k) (K := K) (Ω := Ω) p) (v : NK.GlobalCFT.Place k),
      p • Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x = 0 := by
    intro x v
    exact Phi0.phiColim_smul_p (k := k) (K := K) (Ω := Ω) p
      (Phi0.cOfFun (k := k) (K := K) p ζ hζ (fun v' => if v' = v then 1 else 0)) x
  let T : LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      (NK.GlobalCFT.Place k →₀ ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω)))) :=
    { toFun := fun x => Finsupp.onFinset (Classical.choose (hexS x))
        (fun v => ⟨Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x,
          (mem_pTor).mpr (hpt x v)⟩)
        (fun v hv => Classical.choose_spec (hexS x) v
          (fun h => hv (Subtype.ext h)))
      map_zero' := by
        refine Finsupp.ext (fun v => ?_)
        rw [Finsupp.onFinset_apply, Finsupp.zero_apply]
        exact Subtype.ext (map_zero (Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v))
      map_add' := fun x y => by
        refine Finsupp.ext (fun v => ?_)
        rw [Finsupp.onFinset_apply, Finsupp.add_apply, Finsupp.onFinset_apply,
          Finsupp.onFinset_apply]
        exact Subtype.ext (map_add (Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v) x y) }
  have hT_apply : ∀ (x : LevelCohLimit (k := k) (K := K) (Ω := Ω) p)
      (v : NK.GlobalCFT.Place k),
      (T x) v = ⟨Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x,
        (mem_pTor).mpr (hpt x v)⟩ := by
    intro x v
    exact Finsupp.onFinset_apply (s := Classical.choose (hexS x))
      (f := fun v => ⟨Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x,
        (mem_pTor).mpr (hpt x v)⟩)
      (hf := fun v hv => Classical.choose_spec (hexS x) v (fun h => hv (Subtype.ext h)))
      (a := v)
  have hT_val : ∀ (x : LevelCohLimit (k := k) (K := K) (Ω := Ω) p)
      (v : NK.GlobalCFT.Place k),
      (((T x) v : ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω)))) :
        ClassLevelLimit (k := k) (K := K) (Ω := Ω))
        = Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x :=
    fun x v => congrArg Subtype.val (hT_apply x v)
  have hT_inj : Function.Injective T := by
    intro x y hxy
    have hsub : x - y = 0 := by
      by_contra hne
      obtain ⟨v, hv⟩ := P3 (x - y) hne
      refine hv ?_
      have h1 : (T (x - y)) v = 0 := by
        rw [map_sub, hxy, sub_self, Finsupp.zero_apply]
      have h2 : (((T (x - y)) v : ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω)))) :
          ClassLevelLimit (k := k) (K := K) (Ω := Ω)) = 0 := by
        rw [h1]; rfl
      rw [hT_val (x - y) v] at h2
      exact h2
    exact sub_eq_zero.mp hsub
  let Λ := lamColim (k := k) (K := K) (Ω := Ω) p lam hcompat
  let Λt : LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) :=
    { toFun := fun x => ⟨Λ x, (mem_pTor).mpr (by
          rw [← map_nsmul, Phi0.levelCohLimit_smul_p, map_zero])⟩
      map_zero' := Subtype.ext (map_zero Λ)
      map_add' := fun x y => Subtype.ext (map_add Λ x y) }
  have hB : ∀ y : ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))), p • y = 0 :=
    fun y => Subtype.ext y.2
  let e : ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω) :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun a b => rfl }
  obtain ⟨n, hn⟩ := Phi0.torsion_extend (p := p)
    (V := LevelCohLimit (k := k) (K := K) (Ω := Ω) p)
    (B := ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))))
    (C := ClassLevelLimit (k := k) (K := K) (Ω := Ω))
    hB e T hT_inj Λt P4
  let f : NK.GlobalCFT.Place k → ZMod p := fun v => (n v : ZMod p)
  refine ⟨Phi0.cOfFun (k := k) (K := K) p ζ hζ f, ?_⟩
  have hmain : Phi0.phiColim (k := k) (K := K) (Ω := Ω) p
      (Phi0.cOfFun (k := k) (K := K) p ζ hζ f) = Λ := by
    apply AddMonoidHom.ext
    intro x
    obtain ⟨S, hS, hpair⟩ := P2 f x
    have hS0 : ∀ v : NK.GlobalCFT.Place k,
        Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x ≠ 0 →
          v ∈ Classical.choose (hexS x) := Classical.choose_spec (hexS x)
    have hsupp : (T x).support ⊆ Classical.choose (hexS x) ∪ S := by
      intro v hv
      rw [Finsupp.mem_support_iff] at hv
      exact Finset.mem_union_left S (hS0 v (fun h0 => hv (by
        rw [hT_apply x v]
        exact Subtype.ext h0)))
    have hsum := Finsupp.sum_of_support_subset (T x) hsupp
      (fun i y => n i • (y : ClassLevelLimit (k := k) (K := K) (Ω := Ω)))
      (fun i hi => by simp)
    calc Phi0.phiColim (k := k) (K := K) (Ω := Ω) p
          (Phi0.cOfFun (k := k) (K := K) p ζ hζ f) x
        = ∑ v ∈ S, (f v).val • Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x := hpair
      _ = ∑ v ∈ S, n v • Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x := by
            apply Finset.sum_congr rfl
            intro v hv
            dsimp only [f]
            rw [ZMod.val_natCast]
            exact nsmul_mod_eq_nsmul _ (hpt x v) (n v)
      _ = ∑ v ∈ Classical.choose (hexS x) ∪ S,
            n v • Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x := by
            refine Finset.sum_subset (s₁ := S) (s₂ := Classical.choose (hexS x) ∪ S)
              (f := fun v => n v • Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x)
              Finset.subset_union_right ?_
            intro v hv hvs
            rw [hS v hvs, smul_zero]
      _ = ∑ v ∈ Classical.choose (hexS x) ∪ S,
            n v • (((T x) v : ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω)))) :
              ClassLevelLimit (k := k) (K := K) (Ω := Ω)) :=
            Finset.sum_congr rfl (fun v hv => by rw [hT_val x v])
      _ = (T x).sum (fun i y => n i • (y : ClassLevelLimit (k := k) (K := K) (Ω := Ω))) :=
            hsum.symm
      _ = Λ x := (hn x).symm
  intro L _instNF _instFD _instG h
  let Lv : Lvl k K Ω := ⟨L, _instNF, _instFD, _instG⟩
  have key : ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) Lv
      (phiTriv (k := k) (K := K) (L := L) (ZMod p)
        (Abelian.Ext.mk₀ (Phi0.cOfFun (k := k) (K := K) p ζ hζ f)) h)
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) Lv (lam L h) := by
    rw [← Phi0.phiColim_of (k := k) (K := K) (Ω := Ω) p
      (Phi0.cOfFun (k := k) (K := K) p ζ hζ f) Lv h]
    rw [hmain]
    dsimp only [Λ]
    exact lamColim_of (k := k) (K := K) (Ω := Ω) p lam hcompat Lv h
  exact Phi0.ClassLevelLimit_of_injective Lv key

end Assembly

/-- **E4Ω.** Base case: `φ⁰` is onto for `M = 𝔽_p` (trivial action), `μ_p ⊆ k`: a `p`-torsion
family of functionals `H²(Gal(L/k), 𝔽_p) → H²(Gal(L/k), C_L)` over the levels `K ≤ L ≤ Ω`,
compatible with inflation along inclusions of levels, is the cup product with one
`c ∈ Hom_G(𝔽_p, C_K)`. -/
theorem phi0_trivial_epi_in (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2 →+ extH (classesK k L) 2)
    (hp : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2), p • lam L h = 0)
    (hcompat : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L] (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L'] (hLL : L ≤ L')
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
      inflCIn (k := k) hLL (lam L h) = lam L' (inflTrivIn (k := k) hLL (ZMod p) h)) :
    ∃ c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K,
      ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
        phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c) h = lam L h := by
  obtain ⟨c, hc⟩ := Phi0.phi0_of_pieces (k := k) (K := K) (Ω := Ω) p ζ hζ
    (fun f x => E5Route.pairing_formula p k K Ω ζ hζ f x)
    (fun x hx => phi0_lamV_separates p k K Ω ζ hζ x hx)
    (fun φ => phi0_pTor_scalar p k K Ω φ)
    lam hp hcompat
  exact ⟨c, hc⟩

end Work.SSGRoute
