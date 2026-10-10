import Mathlib
import Submission.Work.MotA.Defs
import Submission.Work.MotA.coheight_eq_one_iff
import Submission.Work.MotA.mvPoly_map_C_isPrime
import Submission.Work.MotA.stabAlgEquiv_rename_castAdd
import Submission.Work.MotA.renameCastAddProj_rename

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.MotA

open MvPolynomial

/-!  ### Auxiliary ring theory for the stabilisation `f = MvPolynomial.rename (Fin.castAdd k)`

Let `R = 𝕜[x₁,…,xₙ]`, `S = 𝕜[x₁,…,x_{n+k}]` and `f = MvPolynomial.rename (Fin.castAdd k) : R →+* S`,
so that `S` is the polynomial ring `R[y₁,…,y_k]` in `k` new variables over `R`.  The proof of
`divCount_rename` rests on:

* `f` is injective (`renameCastAdd_inj`);
* an ideal of `R` meets its extension along `f` in itself (`comap_map_renameCastAdd_eq_self`);
* the extension of a prime ideal of `R` along `f` is prime (`renameCastAdd_isPrime`), transported
  from `Work.MotA.mvPoly_map_C_isPrime` along the algebra equivalence `Work.MotA.stabAlgEquiv`;
* consequently a height-one prime `P ∋ f F` (`F ≠ 0`) is the extension of `p = P ∩ R`, which again
  has height one (`height_comap_renameCastAdd`).

The bijection of the two sets counted in the statement is then `Set.ncard_congr` along `P ↦ P ∩ R`.
-/

/-- The stabilisation map `f = MvPolynomial.rename (Fin.castAdd k)` is injective. -/
lemma renameCastAdd_inj (𝕜 : Type) [Field 𝕜] (n k : ℕ) :
    Function.Injective (MvPolynomial.rename (Fin.castAdd k) :
      MvPolynomial (Fin n) 𝕜 → MvPolynomial (Fin (n + k)) 𝕜) :=
  MvPolynomial.rename_injective _ (Fin.castAdd_injective n k)

/-- An ideal of `𝕜[x₁,…,xₙ]` meets its extension along the stabilisation `f` in itself. -/
lemma comap_map_renameCastAdd_eq_self (𝕜 : Type) [Field 𝕜] (n k : ℕ)
    (I : Ideal (MvPolynomial (Fin n) 𝕜)) :
    Ideal.comap (MvPolynomial.rename (Fin.castAdd k))
      (Ideal.map (MvPolynomial.rename (Fin.castAdd k)) I) = I := by
  refine le_antisymm ?_ Ideal.le_comap_map
  intro x hx
  rw [Ideal.mem_comap] at hx
  have h' : MvPolynomial.rename (Fin.castAdd k) x ∈ Ideal.comap (renameCastAddProj 𝕜 n k) I :=
    Ideal.map_le_comap_of_inverse
      (MvPolynomial.rename (Fin.castAdd k) : MvPolynomial (Fin n) 𝕜 →ₐ[𝕜]
        MvPolynomial (Fin (n + k)) 𝕜)
      (renameCastAddProj 𝕜 n k) I (renameCastAddProj_rename 𝕜 n k) hx
  rw [Ideal.mem_comap] at h'
  rwa [renameCastAddProj_rename 𝕜 n k x] at h'

/-- The stabilisation `f` reflects units. -/
lemma renameCastAdd_isUnit_reflect (𝕜 : Type) [Field 𝕜] (n k : ℕ)
    {r : MvPolynomial (Fin n) 𝕜} (h : IsUnit (MvPolynomial.rename (Fin.castAdd k) r)) :
    IsUnit r := by
  have h2 : IsUnit (renameCastAddProj 𝕜 n k (MvPolynomial.rename (Fin.castAdd k) r)) :=
    h.map (renameCastAddProj 𝕜 n k)
  rwa [renameCastAddProj_rename 𝕜 n k r] at h2

/-- The extension of a prime ideal along the stabilisation `f` is prime. -/
lemma renameCastAdd_isPrime (𝕜 : Type) [Field 𝕜] (n k : ℕ)
    {p : Ideal (MvPolynomial (Fin n) 𝕜)} (hp : p.IsPrime) :
    (Ideal.map (MvPolynomial.rename (Fin.castAdd k)) p).IsPrime := by
  let Θ' : MvPolynomial (Fin (n + k)) 𝕜 ≃+* MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜) :=
    (stabAlgEquiv 𝕜 n k).toRingEquiv
  let Θ : MvPolynomial (Fin (n + k)) 𝕜 →+* MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜) :=
    Θ'.toRingHom
  let fR : MvPolynomial (Fin n) 𝕜 →+* MvPolynomial (Fin (n + k)) 𝕜 :=
    (MvPolynomial.rename (Fin.castAdd k)).toRingHom
  have hcomp : Θ.comp fR =
      (MvPolynomial.C : MvPolynomial (Fin n) 𝕜 →+*
        MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)) := by
    apply RingHom.ext
    intro r
    exact stabAlgEquiv_rename_castAdd 𝕜 n k r
  have h1 : Ideal.map Θ (Ideal.map fR p) =
      Ideal.map (MvPolynomial.C : MvPolynomial (Fin n) 𝕜 →+*
        MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)) p := by
    rw [Ideal.map_map, hcomp]
  have h2 : (Ideal.map (MvPolynomial.C : MvPolynomial (Fin n) 𝕜 →+*
      MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)) p).IsPrime :=
    mvPoly_map_C_isPrime (MvPolynomial (Fin n) 𝕜) (Fin k) hp
  haveI : (Ideal.map Θ (Ideal.map fR p)).IsPrime := by
    rw [h1]; exact h2
  have h3 : Ideal.comap Θ (Ideal.map Θ (Ideal.map fR p)) = Ideal.map fR p :=
    Ideal.comap_map_of_bijective Θ Θ'.bijective
  have h4 : (Ideal.map fR p).IsPrime := by
    rw [← h3]
    exact Ideal.comap_isPrime Θ (Ideal.map Θ (Ideal.map fR p))
  exact h4

/-- **Key lemma.**  A height-one prime `P` of `𝕜[x₁,…,x_{n+k}]` containing the stabilised `F`
(`F ≠ 0`) is the extension of its contraction `p = P ∩ 𝕜[x₁,…,xₙ]`, which again has height one. -/
lemma height_comap_renameCastAdd (𝕜 : Type) [Field 𝕜] (n k : ℕ)
    (F : MvPolynomial (Fin n) 𝕜) (hF : F ≠ 0)
    (P : Ideal (MvPolynomial (Fin (n + k)) 𝕜)) (hP : P.IsPrime) (hP1 : P.height = 1)
    (hFP : MvPolynomial.rename (Fin.castAdd k) F ∈ P) :
    (Ideal.comap (MvPolynomial.rename (Fin.castAdd k)) P).height = 1 ∧
      (Ideal.comap (MvPolynomial.rename (Fin.castAdd k)) P).map
        (MvPolynomial.rename (Fin.castAdd k)) = P := by
  haveI : P.IsPrime := hP
  let f : MvPolynomial (Fin n) 𝕜 →ₐ[𝕜] MvPolynomial (Fin (n + k)) 𝕜 :=
    MvPolynomial.rename (Fin.castAdd k)
  let p := Ideal.comap f P
  haveI hpP : p.IsPrime := inferInstance
  have hFp : F ∈ p := Ideal.mem_comap.mpr hFP
  have hfinj : Function.Injective f := fun a b hab => renameCastAdd_inj 𝕜 n k hab
  have hfF : f F ≠ 0 := fun h => hF (hfinj (by rw [h, map_zero]))
  have hpne : p ≠ ⊥ := fun h => hF (Ideal.mem_bot.mp (h ▸ hFp))
  have hmapne : p.map f ≠ ⊥ := by
    intro h
    have : f F ∈ p.map f := Ideal.mem_map_of_mem f hFp
    rw [h] at this
    exact hfF (Ideal.mem_bot.mp this)
  have hpSprime : (p.map f).IsPrime := renameCastAdd_isPrime 𝕜 n k hpP
  have hpSle : p.map f ≤ P := Ideal.map_comap_le
  -- Step 1: `p · S = P`, because otherwise `p · S` would be a prime strictly between `0` and `P`
  have heq : p.map f = P := by
    by_contra hne
    have hlt : p.map f < P := lt_of_le_of_ne hpSle hne
    have h1 : (p.map f).height < (1 : ℕ∞) :=
      (Ideal.height_le_iff (p := P) (n := 1)).mp (le_of_eq hP1) (p.map f) hpSprime hlt
    have h2 : (1 : ℕ∞) ≤ (p.map f).height := by
      rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      exact hmapne
    exact absurd h1 (not_lt.mpr h2)
  -- Step 2: `p` has height one
  have hle1 : p.height ≤ 1 := by
    refine (Ideal.height_le_iff (p := p) (n := 1)).mpr ?_
    intro q hq hqp
    haveI : q.IsPrime := hq
    by_cases hqbot : q = ⊥
    · rw [hqbot, Ideal.height_bot]
      exact zero_lt_one
    · exfalso
      have hqSprime : (q.map f).IsPrime := renameCastAdd_isPrime 𝕜 n k hq
      have hqSle : q.map f ≤ P := by rw [← heq]; exact Ideal.map_mono hqp.le
      have hqSne : q.map f ≠ P := by
        intro h
        have h1 : Ideal.comap f (Ideal.map f q) = q :=
          comap_map_renameCastAdd_eq_self 𝕜 n k q
        have hc : q = p :=
          calc q = Ideal.comap f (Ideal.map f q) := h1.symm
            _ = Ideal.comap f P := congrArg (Ideal.comap f) h
            _ = p := rfl
        exact hqp.ne hc
      have hlt : q.map f < P := lt_of_le_of_ne hqSle hqSne
      have h1 : (q.map f).height < (1 : ℕ∞) :=
        (Ideal.height_le_iff (p := P) (n := 1)).mp (le_of_eq hP1) (q.map f) hqSprime hlt
      have h2 : (1 : ℕ∞) ≤ (q.map f).height := by
        rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
        intro hbot
        exact hqbot ((Ideal.map_eq_bot_iff_of_injective (renameCastAdd_inj 𝕜 n k)).mp hbot)
      exact absurd h1 (not_lt.mpr h2)
  have hge1 : 1 ≤ p.height := by
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact hpne
  exact ⟨le_antisymm hle1 hge1, heq⟩

/-- The prime `(f p) ⊆ 𝕜[x₁,…,x_{n+k}]` attached to a prime element `p` has height one. -/
lemma height_span_singleton_renameCastAdd (𝕜 : Type) [Field 𝕜] (n k : ℕ)
    {p : MvPolynomial (Fin n) 𝕜} (hp : Prime p) :
    (Ideal.span {MvPolynomial.rename (Fin.castAdd k) p}).height = 1 :=
  Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr
      (fun h => hp.ne_zero (renameCastAdd_inj 𝕜 n k (by simpa using h))))
    (fun hu => hp.not_isUnit (renameCastAdd_isUnit_reflect 𝕜 n k hu))

/-- **`A3`, the stabilisation census.**

`Work.MotA.divCount 𝕜 n F z` counts the codimension-one points of `𝔸ⁿ = Spec 𝕜[x₁,…,xₙ]` at which
`F` vanishes whose residue field is `𝕜`-isomorphic to `κ(z)`; `Work.MotA.polySpec` is `𝔸ⁿ` in the
`PrimeSpectrum` model.  `MvPolynomial.rename (Fin.castAdd k)` views a polynomial in `n` variables as
a polynomial in `n + k` variables (not involving the last `k`).

**Claim.** For `F ≠ 0`, `divCount` of the stabilised polynomial equals the number of
codimension-one points `x` of `𝔸ⁿ` on `V(F)` for which the extension
`x.asIdeal.map (rename (Fin.castAdd k))` — a prime ideal of `𝕜[x₁,…,x_{n+k}]` — is the ideal of a
point whose residue field has the class of `z`.

Route.  Let `S = 𝕜[x₁,…,x_{n+k}]`, viewed as a polynomial ring `𝕜[x₁,…,xₙ][y₁,…,y_k]` over
`R = 𝕜[x₁,…,xₙ]`; the extension `R → S` is injective and free, hence flat and faithfully flat, so
`Ideal.height (P ∩ R) = Ideal.height P` for every prime `P` of `S`.  Because `F ≠ 0`, any
codimension-one prime `P` of `S` with `rename F ∈ P` has `p := P ∩ R` nonzero (it contains `F`),
so `Ideal.height p = Ideal.height P = 1` and `p.map (rename (Fin.castAdd k)) ⊆ P` are both
height-one primes, whence `P = p.map (rename (Fin.castAdd k))` (a strict inclusion of primes
strictly increases height).  Conversely the extension of a height-one prime of `R` is prime of
height one.  This gives a bijection between the two sets of points, matching the conditions
`F ∈ x.asIdeal`, `rename F ∈ y.asIdeal` and `ResEquiv 𝕜 y z`; conclude with `Set.ncard_congr` (or
`Set.ncard_image_of_injective`), using that a point of `Spec` is determined by its ideal and
`MvPolynomial.rename_injective` (`Fin.castAdd_injective`).  The hypothesis `F ≠ 0` is necessary:
for `F = 0` the claim fails (with `𝕜 = 𝔽₂`, `n = 0`, `k = 1` and `z` the unique point of
`Spec 𝔽₂` the left-hand side is `2` while the right-hand side is empty). -/
theorem divCount_rename (𝕜 : Type) [Field 𝕜] (n k : ℕ) (F : MvPolynomial (Fin n) 𝕜)
    (hF : F ≠ 0) {Z : AlgebraicGeometry.Scheme.{0}}
    [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (z : Z) :
    Work.MotA.divCount 𝕜 (n + k) (MvPolynomial.rename (Fin.castAdd k) F) z =
      Set.ncard {x : Work.MotA.polySpec 𝕜 n | Order.coheight x = 1 ∧ F ∈ x.asIdeal ∧
        ∃ y : Work.MotA.polySpec 𝕜 (n + k),
          y.asIdeal = x.asIdeal.map (MvPolynomial.rename (Fin.castAdd k)) ∧ ResEquiv 𝕜 y z} := by
  classical
  let f : MvPolynomial (Fin n) 𝕜 →ₐ[𝕜] MvPolynomial (Fin (n + k)) 𝕜 :=
    MvPolynomial.rename (Fin.castAdd k)
  let A : Set (polySpec 𝕜 (n + k)) :=
    {y | Order.coheight y = 1 ∧ f F ∈ y.asIdeal ∧ ResEquiv 𝕜 y z}
  let B : Set (polySpec 𝕜 n) :=
    {x | Order.coheight x = 1 ∧ F ∈ x.asIdeal ∧
      ∃ y : polySpec 𝕜 (n + k), y.asIdeal = x.asIdeal.map f ∧ ResEquiv 𝕜 y z}
  let φ : polySpec 𝕜 (n + k) → polySpec 𝕜 n :=
    fun y => ⟨y.asIdeal.comap f, by
      haveI : y.asIdeal.IsPrime := y.isPrime
      exact Ideal.comap_isPrime f y.asIdeal⟩
  have hset : divCount 𝕜 (n + k) (MvPolynomial.rename (Fin.castAdd k) F) z = A.ncard := rfl
  rw [hset]
  change A.ncard = B.ncard
  refine Set.ncard_congr (s := A) (t := B) (fun y _ => φ y) ?_ ?_ ?_
  · -- image: the contraction of a point of `A` lies in `B`
    intro y hy
    simp only [A, Set.mem_setOf_eq] at hy
    obtain ⟨hcoh, hmem, hres⟩ := hy
    have hP1 : y.asIdeal.height = 1 := by
      rw [AlgebraicGeometry.idealHeight_eq_coheight]; exact hcoh
    obtain ⟨hp1, hmap⟩ :=
      height_comap_renameCastAdd 𝕜 n k F hF y.asIdeal y.isPrime hP1 hmem
    simp only [B, Set.mem_setOf_eq]
    refine ⟨?_, ?_, y, hmap.symm, hres⟩
    · rw [← AlgebraicGeometry.idealHeight_eq_coheight]
      exact hp1
    · exact Ideal.mem_comap.mpr hmem
  · -- injectivity: a height-one prime containing `f F` is determined by its contraction
    intro y₁ y₂ hy₁ hy₂ heq
    have h1 : y₁.asIdeal.comap f = y₂.asIdeal.comap f := congrArg PrimeSpectrum.asIdeal heq
    simp only [A, Set.mem_setOf_eq] at hy₁ hy₂
    obtain ⟨hc₁, hm₁, _⟩ := hy₁
    obtain ⟨hc₂, hm₂, _⟩ := hy₂
    have hP₁ : y₁.asIdeal.height = 1 := by
      rw [AlgebraicGeometry.idealHeight_eq_coheight]; exact hc₁
    have hP₂ : y₂.asIdeal.height = 1 := by
      rw [AlgebraicGeometry.idealHeight_eq_coheight]; exact hc₂
    obtain ⟨_, hmap₁⟩ := height_comap_renameCastAdd 𝕜 n k F hF y₁.asIdeal y₁.isPrime hP₁ hm₁
    obtain ⟨_, hmap₂⟩ := height_comap_renameCastAdd 𝕜 n k F hF y₂.asIdeal y₂.isPrime hP₂ hm₂
    exact PrimeSpectrum.ext (by rw [← hmap₁, h1, hmap₂])
  · -- surjectivity: every point of `B` comes from its witnessing point
    intro b hb
    simp only [B, Set.mem_setOf_eq] at hb
    obtain ⟨hcoh, hmem, y, hyid, hres⟩ := hb
    obtain ⟨p, hp, hbsp⟩ := (coheight_eq_one_iff 𝕜 n b).mp hcoh
    have hspan : (Ideal.span {p}).map f = Ideal.span {f p} := by
      rw [Ideal.map_span]
      simp
    have hy1 : y.asIdeal.height = 1 := by
      rw [hyid, hbsp, hspan]
      exact height_span_singleton_renameCastAdd 𝕜 n k hp
    have hyA : y ∈ A := by
      simp only [A, Set.mem_setOf_eq]
      exact ⟨by rw [← AlgebraicGeometry.idealHeight_eq_coheight]; exact hy1,
        by rw [hyid]; exact Ideal.mem_map_of_mem f hmem, hres⟩
    refine ⟨y, hyA, ?_⟩
    show φ y = b
    refine PrimeSpectrum.ext ?_
    show y.asIdeal.comap f = b.asIdeal
    rw [hyid]
    exact comap_map_renameCastAdd_eq_self 𝕜 n k b.asIdeal

end Work.MotA

end
