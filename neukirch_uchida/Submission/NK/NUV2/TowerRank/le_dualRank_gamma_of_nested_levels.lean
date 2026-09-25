import Mathlib
import Submission.NK.NUV2.TowerRank.towerIso
import Submission.NK.NUV2.TowerRank.towerCompatible
import Submission.NK.NUV2.TowerRank.le_dualRank_of_surjective
import Submission.NK.Reconstruct.GammaObject
import Submission.NK.Reconstruct.proj_surjective
import Submission.NK.Reconstruct.ellRestrict_surjective
import Submission.NK.RankTheoryDeep.exists_addHom_padicInt_lift
import Submission.NK.RankTheoryDeep.continuous_of_toZModPow_comp

/-!
# `r ≤ dualRank Γ_K 2` from a nested tower of levels with ℓ-part `(ℤ/2^n)^r`

This file proves `NK.NUV2.TowerRank.le_dualRank_gamma_of_nested_levels`: half (B) of the rank
form of `2`-adic Artin reciprocity (`Submission/Work/NUV2/TowerRank/NOTES.md` §3) in *tower* form.

Given a nested sequence of finite normal levels `L n / K` of a separable closure `Ω ⊇ K` whose
`2`-primary abelianised parts are `(ℤ/2^n)^r`, the `ℤ_2`-rank of the continuous dual of Shimizu's
`Γ_K = lim_n ℓ-part(Gal(L/K)^ab)` is at least `r`.

The proof uses the group-theoretic crux `TowerCompatible r`
(`Submission/Work/NUV2/TowerRank/towerCompatible.lean`): the *level-wise* isomorphisms
`ℓ-part(Gal(L n/K)^ab) ≅ (ℤ/2^n)^r` can be corrected to a family compatible with the transition
maps of the tower.  With the corrected family `φ n` the composites
`φ n ∘ proj_n : Γ_K →* (ℤ/2^n)^r` form a coherent inverse system with *the standard* reduction
maps `(ℤ/2^{n+1})^r → (ℤ/2^n)^r`, hence

* each coordinate lifts (via the additive universal property of `ℤ_2 = lim_n ℤ/2^n`,
  `NK.RankTheoryDeep.exists_addHom_padicInt_lift`) to a continuous character
  `χ_i : Γ_K →+ ℤ_2` (`NK.RankTheoryDeep.continuous_of_toZModPow_comp`);
* the map `x ↦ (χ_i x)_i : Γ_K → ℤ_2^r` is surjective, by the finite intersection property of the
  compact group `Γ_K` (its `n`-th reduction is `φ n ∘ proj_n`, which is surjective);
* hence the `χ_i` are `ℤ_2`-linearly independent, which is
  `NK.NUV2.TowerRank.le_dualRank_of_surjective`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.NUV2.TowerRank

open scoped Topology

/-! ## The standard reduction of `ℤ/2^n`-coefficients

The reduction `ℤ/2^n → ℤ/2^m` (`m ≤ n`) is needed as a *function of `m` and `n` only*, so that it
can be iterated along a tower without dragging divisibility proofs through the statements.  It is
therefore defined by a `dite` (the impossible branch being filled with `0`); all its properties are
proved from the `if_pos` case, and the resulting maps are compared using that
`ℤ/2^n →+* ℤ/2^m` is a subsingleton for each pair. -/

/-- **The reduction `ℤ/2^n →+ ℤ/2^m` for `m ≤ n`**, as an additive homomorphism depending only on
`m` and `n`. -/
noncomputable def redAdd (m n : ℕ) : ZMod (2 ^ n) →+ ZMod (2 ^ m) :=
  if h : m ≤ n then
    { toFun := fun x => ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ m)) x
      map_zero' := (ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ m))).map_zero
      map_add' := fun a b => (ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ m))).map_add a b }
  else 0

/-- The defining property of `redAdd` in the case that matters. -/
lemma redAdd_of_le {m n : ℕ} (h : m ≤ n) (x : ZMod (2 ^ n)) :
    redAdd m n x = ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ m)) x := by
  rw [redAdd, dif_pos h]
  rfl

/-- `redAdd m m` is the identity. -/
lemma redAdd_self (m : ℕ) (x : ZMod (2 ^ m)) : redAdd m m x = x := by
  have h : ZMod.castHom (pow_dvd_pow 2 (le_refl m)) (ZMod (2 ^ m))
      = RingHom.id (ZMod (2 ^ m)) := Subsingleton.elim _ _
  calc redAdd m m x = ZMod.castHom (pow_dvd_pow 2 (le_refl m)) (ZMod (2 ^ m)) x :=
        redAdd_of_le le_rfl x
    _ = (RingHom.id (ZMod (2 ^ m))) x := by rw [h]
    _ = x := by simp

/-- `redAdd` is transitive. -/
lemma redAdd_comp {m k n : ℕ} (h1 : m ≤ k) (h2 : k ≤ n) (x : ZMod (2 ^ n)) :
    redAdd m k (redAdd k n x) = redAdd m n x := by
  have hcomp : (ZMod.castHom (pow_dvd_pow 2 h1) (ZMod (2 ^ m))).comp
      (ZMod.castHom (pow_dvd_pow 2 h2) (ZMod (2 ^ k)))
      = ZMod.castHom (pow_dvd_pow 2 (h1.trans h2)) (ZMod (2 ^ m)) := by
    rw [ZMod.castHom_comp]
  rw [redAdd_of_le h1, redAdd_of_le h2, redAdd_of_le (h1.trans h2), ← RingHom.comp_apply, hcomp]

/-- **Coordinatewise reduction** of `r`-tuples, the transition map of the standard `(ℤ/2^n)^r`
tower. -/
noncomputable def coordRed (r m n : ℕ) : (Fin r → ZMod (2 ^ n)) →+ (Fin r → ZMod (2 ^ m)) where
  toFun := fun x i => redAdd m n (x i)
  map_zero' := by ext i; simp
  map_add' := fun a b => by ext i; simp

@[simp] lemma coordRed_apply (r m n : ℕ) (x : Fin r → ZMod (2 ^ n)) (i : Fin r) :
    coordRed r m n x i = redAdd m n (x i) := rfl

lemma coordRed_self (r m : ℕ) (x : Fin r → ZMod (2 ^ m)) : coordRed r m m x = x := by
  funext i
  simp [redAdd_self]

lemma coordRed_comp (r m k n : ℕ) (h1 : m ≤ k) (h2 : k ≤ n)
    (x : Fin r → ZMod (2 ^ n)) : coordRed r m k (coordRed r k n x) = coordRed r m n x := by
  funext i
  simp only [coordRed_apply]
  exact redAdd_comp h1 h2 (x i)

/-- **The standard transition map** `(ℤ/2^{n+1})^r → (ℤ/2^n)^r` of the tower, as a multiplicative
homomorphism (the shape in which `TowerCompatible` consumes it). -/
noncomputable def towerRed (r n : ℕ) :
    Multiplicative (Fin r → ZMod (2 ^ (n + 1))) →* Multiplicative (Fin r → ZMod (2 ^ n)) :=
  AddMonoidHom.toMultiplicative (coordRed r n (n + 1))

@[simp] lemma towerRed_toAdd (r n : ℕ) (x : Multiplicative (Fin r → ZMod (2 ^ (n + 1)))) :
    (towerRed r n x).toAdd = coordRed r n (n + 1) x.toAdd := rfl

/-- The standard transition maps are surjective. -/
lemma towerRed_surjective (r n : ℕ) : Function.Surjective (towerRed r n) := by
  intro y
  have hy : ∀ i : Fin r, ∃ x : ZMod (2 ^ (n + 1)),
      ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n)) x = y.toAdd i :=
    fun i => ZMod.castHom_surjective (pow_dvd_pow 2 (Nat.le_succ n)) (y.toAdd i)
  choose x hx using hy
  refine ⟨Multiplicative.ofAdd x, ?_⟩
  have : (towerRed r n (Multiplicative.ofAdd x)).toAdd = y.toAdd := by
    funext i
    rw [towerRed_toAdd, coordRed_apply, redAdd_of_le (Nat.le_succ n)]
    exact hx i
  exact Multiplicative.toAdd.injective this

theorem le_dualRank_gamma_of_nested_levels (r : ℕ) (hTower : NK.NUV2.TowerRank.TowerCompatible r)
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsGalois K Ω]
    (L : ℕ → NK.Reconstruct.FrobLevel K Ω)
    (hnest : ∀ n, (L n).L ≤ (L (n+1)).L)
    (hlev : ∀ n, Nonempty (NK.Reconstruct.LevelEllPart (L n).L 2 ≃*
        Multiplicative (Fin r → ZMod (2^n)))) :
    (r : Cardinal) ≤ NK.RankTheoryDeep.dualRank (NK.Reconstruct.Gamma K Ω 2) 2 := by
  classical
  haveI hGfin : ∀ n, Fintype (NK.Reconstruct.LevelEllPart (L n).L 2) :=
    fun n => Fintype.ofFinite _
  -- The tower of levels, the standard tower `(ℤ/2^n)^r`, and the corrected compatible
  -- isomorphisms supplied by `TowerCompatible r`.
  let G : ℕ → Type := fun n => NK.Reconstruct.LevelEllPart (L n).L 2
  let H : ℕ → Type := fun n => Multiplicative (Fin r → ZMod (2 ^ n))
  let qG : ∀ n, G (n + 1) →* G n :=
    fun n => NK.Reconstruct.ellRestrict 2 (L n) (L (n + 1)) (hnest n)
  let isoG : ∀ n, G n ≃* Multiplicative (Fin r → ZMod (2 ^ n)) := fun n => (hlev n).some
  let isoH : ∀ n, H n ≃* Multiplicative (Fin r → ZMod (2 ^ n)) := fun n => MulEquiv.refl _
  let eGH : ∀ n, G n ≃* H n := fun n => (isoG n).trans (isoH n).symm
  have hqG : ∀ n, Function.Surjective (qG n) :=
    fun n => NK.Reconstruct.projSurj_ellRestrict_surj 2 (hnest n)
  have hqH : ∀ n, Function.Surjective (towerRed r n) := fun n => towerRed_surjective r n
  obtain ⟨φ, hφ⟩ := hTower G H qG (fun n => towerRed r n) hqG hqH isoG isoH eGH
  -- The level maps `Γ_K → (ℤ/2^n)^r`, compatible with the *standard* reductions.
  let F : ∀ n, Additive (NK.Reconstruct.Gamma K Ω 2) →+ (Fin r → ZMod (2 ^ n)) := fun n =>
    { toFun := fun x => ((φ n) (NK.Reconstruct.Gamma.proj (L n) (Additive.toMul x))).toAdd
      map_zero' := by
        show ((φ n) (NK.Reconstruct.Gamma.proj (L n) (Additive.toMul 0))).toAdd = 0
        simp
      map_add' := by
        intro x y
        show ((φ n) (NK.Reconstruct.Gamma.proj (L n) (Additive.toMul (x + y)))).toAdd
            = ((φ n) (NK.Reconstruct.Gamma.proj (L n) (Additive.toMul x))).toAdd
              + ((φ n) (NK.Reconstruct.Gamma.proj (L n) (Additive.toMul y))).toAdd
        rw [toMul_add, map_mul, map_mul, toAdd_mul] }
  -- the step of the tower: the corrected isomorphisms are compatible with the standard
  -- reductions and with the projections.
  have hstep : ∀ n (x : Additive (NK.Reconstruct.Gamma K Ω 2)),
      F n x = coordRed r n (n + 1) (F (n + 1) x) := by
    intro n x
    have hproj : NK.Reconstruct.Gamma.proj (L n) (Additive.toMul x)
        = qG n (NK.Reconstruct.Gamma.proj (L (n + 1)) (Additive.toMul x)) :=
      (NK.Reconstruct.Gamma.proj_compatible (L n) (L (n + 1)) (hnest n)
        (Additive.toMul x)).symm
    have hcomp : (φ n) (qG n (NK.Reconstruct.Gamma.proj (L (n + 1)) (Additive.toMul x)))
        = towerRed r n ((φ (n + 1))
            (NK.Reconstruct.Gamma.proj (L (n + 1)) (Additive.toMul x))) :=
      congrFun (congrArg (fun f : G (n + 1) →* H n => ⇑f) (hφ n))
        (NK.Reconstruct.Gamma.proj (L (n + 1)) (Additive.toMul x))
    show ((φ n) (NK.Reconstruct.Gamma.proj (L n) (Additive.toMul x))).toAdd
        = coordRed r n (n + 1) (((φ (n + 1))
            (NK.Reconstruct.Gamma.proj (L (n + 1)) (Additive.toMul x))).toAdd)
    rw [hproj, hcomp, towerRed_toAdd]
  -- consequently the level maps are coherent.
  have hcompat : ∀ (m n : ℕ) (hmn : m ≤ n) (x : Additive (NK.Reconstruct.Gamma K Ω 2)),
      F m x = coordRed r m n (F n x) := by
    intro m n hmn x
    have key : ∀ k (hmk : m ≤ k), F m x = coordRed r m k (F k x) := by
      intro k hmk
      induction k, hmk using Nat.le_induction with
      | base => rw [coordRed_self]
      | succ j hmj ih =>
          rw [ih, hstep j x]
          exact coordRed_comp r m j (j + 1) hmj (Nat.le_succ j) (F (j + 1) x)
    exact key n hmn
  -- the coordinates, as compatible families of additive characters of `Γ_K`
  let Fi : ∀ (i : Fin r) (n : ℕ),
      Additive (NK.Reconstruct.Gamma K Ω 2) →+ ZMod (2 ^ n) :=
    fun i n => (Pi.evalAddMonoidHom (fun _ : Fin r => ZMod (2 ^ n)) i).comp (F n)
  have hcompatFi : ∀ (i : Fin r) (m n : ℕ) (hmn : m ≤ n)
      (x : Additive (NK.Reconstruct.Gamma K Ω 2)),
      Fi i m x = redAdd m n (Fi i n x) := by
    intro i m n hmn x
    show (F m x) i = redAdd m n ((F n x) i)
    have h := congrFun (hcompat m n hmn x) i
    rwa [coordRed_apply] at h
  have hcompatFi_cast : ∀ (i : Fin r) (m n : ℕ) (hmn : m ≤ n)
      (x : Additive (NK.Reconstruct.Gamma K Ω 2)),
      Fi i m x = ZMod.castHom (pow_dvd_pow 2 hmn) (ZMod (2 ^ m)) (Fi i n x) := by
    intro i m n hmn x
    rw [hcompatFi i m n hmn x, redAdd_of_le hmn]
  have hcontFi : ∀ (i : Fin r) (n : ℕ), Continuous ⇑(Fi i n) := by
    intro i n
    have h1 : Continuous (fun x : Additive (NK.Reconstruct.Gamma K Ω 2) =>
        NK.Reconstruct.Gamma.proj (L n) (Additive.toMul x)) :=
      (NK.Reconstruct.continuous_proj (K := K) (K' := Ω) 2 (L n)).comp
        (continuous_id : Continuous (Additive.toMul : Additive (NK.Reconstruct.Gamma K Ω 2) →
          NK.Reconstruct.Gamma K Ω 2))
    have h2 : Continuous (fun y : NK.Reconstruct.LevelEllPart (L n).L 2 =>
        ((φ n) y).toAdd i) := continuous_of_discreteTopology
    exact h2.comp h1
  -- lift each coordinate along `ℤ_2 = lim_n ℤ/2^n`
  have hlift : ∀ i : Fin r, ∃ g : Additive (NK.Reconstruct.Gamma K Ω 2) →+ PadicInt 2,
      ∀ (n : ℕ) (x : Additive (NK.Reconstruct.Gamma K Ω 2)),
        PadicInt.toZModPow n (g x) = Fi i n x :=
    fun i => NK.RankTheoryDeep.exists_addHom_padicInt_lift (Fi i) (hcompatFi_cast i)
  choose χhom hχhom using hlift
  have hcontχ : ∀ i : Fin r, Continuous ⇑(χhom i) := fun i =>
    NK.RankTheoryDeep.continuous_of_toZModPow_comp (χhom i) (Fi i)
      (fun n => hcontFi i n) (fun n x => hχhom i n x)
  let χ : Fin r → NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω 2) 2 :=
    fun i => ⟨χhom i, hcontχ i⟩
  -- the map `x ↦ (χ_i x)_i` is surjective: its `n`-th reduction is `F n`, which is surjective,
  -- and `Γ_K` is compact.
  refine NK.NUV2.TowerRank.le_dualRank_of_surjective χ (fun y => ?_)
  let S : ℕ → Set (NK.Reconstruct.Gamma K Ω 2) := fun n =>
    {x | ∀ i : Fin r, Fi i n (Additive.ofMul x) = PadicInt.toZModPow n (y i)}
  have hclosed : ∀ n, IsClosed (S n) := by
    intro n
    have hset : S n = ⋂ i : Fin r,
        {x : NK.Reconstruct.Gamma K Ω 2 |
          Fi i n (Additive.ofMul x) = PadicInt.toZModPow n (y i)} := by
      ext x
      simp only [S, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hset]
    refine isClosed_iInter (fun i => isClosed_eq ?_ continuous_const)
    exact (hcontFi i n).comp
      (continuous_id : Continuous (Additive.ofMul : NK.Reconstruct.Gamma K Ω 2 →
        Additive (NK.Reconstruct.Gamma K Ω 2)))
  have hnonempty : ∀ n, (S n).Nonempty := by
    intro n
    obtain ⟨g, hg⟩ := NK.Reconstruct.proj_surjective (K := K) (K' := Ω) 2 (L n)
      ((φ n).symm (Multiplicative.ofAdd (fun i : Fin r => PadicInt.toZModPow n (y i))))
    refine ⟨g, ?_⟩
    intro i
    show ((φ n) (NK.Reconstruct.Gamma.proj (L n) g)).toAdd i = PadicInt.toZModPow n (y i)
    rw [hg, MulEquiv.apply_symm_apply]
    rfl
  have hanti : ∀ {m n : ℕ}, m ≤ n → S n ⊆ S m := by
    intro m n hmn x hx i
    have h1 : Fi i m (Additive.ofMul x) = redAdd m n (Fi i n (Additive.ofMul x)) :=
      hcompatFi i m n hmn (Additive.ofMul x)
    have h2 : redAdd m n (Fi i n (Additive.ofMul x))
        = ZMod.castHom (pow_dvd_pow 2 hmn) (ZMod (2 ^ m)) (Fi i n (Additive.ofMul x)) :=
      redAdd_of_le hmn _
    rw [h1, h2, hx i]
    exact congrFun (congrArg (fun f : ℤ_[2] →+* ZMod (2 ^ m) => ⇑f)
      (PadicInt.zmod_cast_comp_toZModPow m n hmn)) (y i)
  have hInter : (⋂ n, S n).Nonempty := by
    by_contra hne
    have hempty : (Set.univ ∩ ⋂ n, S n) = ∅ := by
      rw [Set.univ_inter]
      exact Set.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨u, hu⟩ := isCompact_univ.elim_finite_subfamily_closed S hclosed
      (Set.disjoint_iff_inter_eq_empty.mpr hempty)
    obtain ⟨x, hx⟩ := hnonempty (u.sup id)
    have hx' : x ∈ Set.univ ∩ ⋂ n ∈ u, S n := by
      refine ⟨Set.mem_univ x, ?_⟩
      rw [Set.mem_iInter₂]
      intro n hn
      exact (hanti (Finset.le_sup hn)) hx
    exact Set.disjoint_left.mp hu hx'.1 hx'.2
  obtain ⟨x, hx⟩ := hInter
  refine ⟨x, ?_⟩
  funext i
  refine PadicInt.ext_of_toZModPow.mp (fun n => ?_)
  exact (hχhom i n (Additive.ofMul x)).trans (Set.mem_iInter.mp hx n i)

end NK.NUV2.TowerRank
