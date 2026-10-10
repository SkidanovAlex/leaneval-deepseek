import Mathlib
import Submission.Work.MotC5N3.Ruling
import Submission.Work.MotC5N3.asY0_curve
import Submission.Work.MotAS.asRulingEval
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.asTheta2_fracTop_of` — the chart-2 ruling presentation generates the function field

The `RatFunc 𝕜 ↦ K` fork of the *proved* `Work.MotV5.ASLocal.asTheta2_fracTop_of`
(`Submission/Work/MotV5/ASLocal/asTheta2_fracTop_of.lean`): the closure of the image of the chart
subalgebra `asR2 D g` inside `RatFunc ↥(twistFieldAS D g)` is everything, from the three
non-degeneracy inputs `hW0` (the normalising coordinate `W 0 ≠ 0`), `hrho` (the non-vanishing of
`kleinRAS` on the ruling point `W/W 0`) and `hrank` (the Möbius determinant of the ruling vectors
`asRuleQA/asRuleQB` at the generic curve point `asY0 D g`).

The proof is the same as the `RatFunc 𝕜`-hardwired one: the constants, the Klein parameters, the
chart coordinates, the curve point, the ruling vectors and the ruling parameter `RatFunc.X` all lie
in the closure `T` of the image of `asR2 D g`; since `RatFunc ↥F = ↥F⟮X⟯`, the whole fraction field
is generated.  Only the three places that mention the base field change: the constants
`K ↦ ↥F ↦ RatFunc ↥F` (`hKm`), the scalars `𝕜` of the Klein parameters (`haT`, `hbT`), and the
`MvPolynomial`-adjoin membership argument `hsub` (which is `K`-linear here).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Work.MotC5N3

/-! ## §1 Membership lemmas: the link data of elements of a subfield stay in the subfield -/

section MemLemmas

/-- The inverse cubic map `kleinRAS` evaluated at elements of a subfield stays in that subfield. -/
theorem kleinRAS_mem {A' : Type*} [Field A'] (S : Subfield A') (a b g : A') (z : Fin 5 → A')
    (ha : a ∈ S) (hb : b ∈ S) (hg : g ∈ S) (hz : ∀ i, z i ∈ S) (k : Fin 5) :
    Work.MotAS.kleinRAS a b g z k ∈ S := by
  have hmain := congrFun (Work.MotAS.map_kleinRAS (S.subtype) (⟨a, ha⟩ : S) (⟨b, hb⟩ : S)
    (⟨g, hg⟩ : S) (fun i => (⟨z i, hz i⟩ : S))) k
  show Work.MotAS.kleinRAS (S.subtype (⟨a, ha⟩ : S)) (S.subtype (⟨b, hb⟩ : S))
      (S.subtype (⟨g, hg⟩ : S)) (fun i => S.subtype (⟨z i, hz i⟩ : S)) k ∈ S
  rw [hmain]
  exact (Work.MotAS.kleinRAS (⟨a, ha⟩ : S) (⟨b, hb⟩ : S) (⟨g, hg⟩ : S)
    (fun i => (⟨z i, hz i⟩ : S)) k).2

/-- `asRuleQA` evaluated at elements of a subfield stays in that subfield. -/
theorem asRuleQA_mem {A' : Type*} [Field A'] (S : Subfield A') (a b g : A') (c : Fin 5 → A')
    (ha : a ∈ S) (hb : b ∈ S) (hg : g ∈ S) (hc : ∀ i, c i ∈ S) (k : Fin 5) :
    Work.MotAS.asRuleQA a b g c k ∈ S := by
  have hmain := Work.MotAS.map_asRuleQA (S.subtype) (⟨a, ha⟩ : S) (⟨b, hb⟩ : S)
    (⟨g, hg⟩ : S) (fun i => (⟨c i, hc i⟩ : S)) k
  show Work.MotAS.asRuleQA (S.subtype (⟨a, ha⟩ : S)) (S.subtype (⟨b, hb⟩ : S))
      (S.subtype (⟨g, hg⟩ : S)) (fun i => S.subtype (⟨c i, hc i⟩ : S)) k ∈ S
  rw [← hmain]
  exact (Work.MotAS.asRuleQA (⟨a, ha⟩ : S) (⟨b, hb⟩ : S) (⟨g, hg⟩ : S)
    (fun i => (⟨c i, hc i⟩ : S)) k).2

/-- `asRuleQB` evaluated at elements of a subfield stays in that subfield. -/
theorem asRuleQB_mem {A' : Type*} [Field A'] (S : Subfield A') (a b g : A') (c : Fin 5 → A')
    (ha : a ∈ S) (hb : b ∈ S) (hg : g ∈ S) (hc : ∀ i, c i ∈ S) (k : Fin 5) :
    Work.MotAS.asRuleQB a b g c k ∈ S := by
  have hmain := Work.MotAS.map_asRuleQB (S.subtype) (⟨a, ha⟩ : S) (⟨b, hb⟩ : S)
    (⟨g, hg⟩ : S) (fun i => (⟨c i, hc i⟩ : S)) k
  show Work.MotAS.asRuleQB (S.subtype (⟨a, ha⟩ : S)) (S.subtype (⟨b, hb⟩ : S))
      (S.subtype (⟨g, hg⟩ : S)) (fun i => S.subtype (⟨c i, hc i⟩ : S)) k ∈ S
  rw [← hmain]
  exact (Work.MotAS.asRuleQB (⟨a, ha⟩ : S) (⟨b, hb⟩ : S) (⟨g, hg⟩ : S)
    (fun i => (⟨c i, hc i⟩ : S)) k).2

end MemLemmas

/-! ## §2 The assembly -/

theorem asTheta2_fracTop_of (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hW0 : Work.MotC5N3.asW2 D g 0 ≠ 0)
    (hrho : Work.MotAS.kleinRAS (Work.MotC5N3.as2a D g) (Work.MotC5N3.as2b D g)
        (Work.MotC5N3.as2g D g)
        (fun j => Work.MotC5N3.asW2 D g j / Work.MotC5N3.asW2 D g 0) ≠ 0)
    (hrank : Work.MotAS.asRuleQA (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.a)
          (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.b)
          (algebraMap K ↥(Work.MotC5N3.twistFieldAS D g) g) (Work.MotC5N3.asY0 D g) 1
        * Work.MotAS.asRuleQB (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.a)
          (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.b)
          (algebraMap K ↥(Work.MotC5N3.twistFieldAS D g) g) (Work.MotC5N3.asY0 D g) 0
        - Work.MotAS.asRuleQA (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.a)
          (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.b)
          (algebraMap K ↥(Work.MotC5N3.twistFieldAS D g) g) (Work.MotC5N3.asY0 D g) 0
        * Work.MotAS.asRuleQB (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.a)
          (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.b)
          (algebraMap K ↥(Work.MotC5N3.twistFieldAS D g) g) (Work.MotC5N3.asY0 D g) 1 ≠ 0) :
    Subfield.closure (Set.range (algebraMap ↥(Work.MotC5N3.asR2 D g)
      (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)))) = ⊤ := by
  classical
  haveI : CharP 𝕜 5 := charP_of_algebra_charP_lemma (𝕜 := 𝕜) (K := K)
  change Subfield.closure (Set.range (algebraMap ↥(asR2 D g) (as2A D g))) = ⊤
  have h5R : (5 : as2A D g) = 0 := by
    have h : algebraMap K (as2A D g) ((5 : ℕ) : K) = 0 := by
      rw [CharP.cast_eq_zero K 5, map_zero]
    simpa only [Nat.cast_ofNat, map_ofNat] using h
  set T : Subfield (as2A D g) :=
    Subfield.closure (Set.range (algebraMap ↥(asR2 D g) (as2A D g))) with hT
  -- the three inputs, in the vocabulary of this file
  have hW0ne : asW2 D g 0 ≠ 0 := hW0
  have hrhon : Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g)
      (fun j => asW2 D g j / asW2 D g 0) ≠ 0 := hrho
  -- the constants of `K` lie in `T`
  have hKm : ∀ k : K, algebraMap K (as2A D g) k ∈ T := by
    intro k
    rw [hT]
    refine Subfield.subset_closure ⟨algebraMap K ↥(asR2 D g) k, ?_⟩
    exact (IsScalarTower.algebraMap_apply K ↥(asR2 D g) (as2A D g) k).symm
  have haT : as2a D g ∈ T := by
    rw [show as2a D g = algebraMap K (as2A D g) (algebraMap 𝕜 K D.a) from
      IsScalarTower.algebraMap_apply 𝕜 K (as2A D g) D.a]
    exact hKm _
  have hbT : as2b D g ∈ T := by
    rw [show as2b D g = algebraMap K (as2A D g) (algebraMap 𝕜 K D.b) from
      IsScalarTower.algebraMap_apply 𝕜 K (as2A D g) D.b]
    exact hKm _
  have hgT : as2g D g ∈ T := by
    rw [show as2g D g = algebraMap K (as2A D g) g from rfl]
    exact hKm g
  -- the chart coordinates lie in `T`
  have hphi : ∀ j : Fin 3, asPhi2 D g j ∈ T := by
    intro j
    rw [hT]
    refine Subfield.subset_closure ⟨⟨asPhi2 D g j, ?_⟩, rfl⟩
    exact Algebra.subset_adjoin (Set.mem_range_self j)
  -- the ruling lines lie in the hyperplane `{z₄ = 0}`, so `W 4 = 0`
  have hW4z : asW2 D g 4 = 0 :=
    Work.MotAS.asRuleQW_four (as2a D g) (as2b D g) (as2g D g) (as2c D g)
      (RatFunc.X : as2A D g)
  -- the normalised ruling coordinates
  have hpsi : ∀ k : Fin 5, asW2 D g k / asW2 D g 0 ∈ T := by
    intro k
    fin_cases k
    · change asW2 D g 0 / asW2 D g 0 ∈ T
      rw [div_self hW0ne]
      exact T.one_mem
    · change asW2 D g 1 / asW2 D g 0 ∈ T
      have h1 : Work.MotAS.asIdx (0 : Fin 3) = (1 : Fin 5) := Fin.ext rfl
      rw [← h1]
      exact hphi 0
    · change asW2 D g 2 / asW2 D g 0 ∈ T
      have h1 : Work.MotAS.asIdx (1 : Fin 3) = (2 : Fin 5) := Fin.ext rfl
      rw [← h1]
      exact hphi 1
    · change asW2 D g 3 / asW2 D g 0 ∈ T
      have h1 : Work.MotAS.asIdx (2 : Fin 3) = (3 : Fin 5) := Fin.ext rfl
      rw [← h1]
      exact hphi 2
    · change asW2 D g 4 / asW2 D g 0 ∈ T
      rw [hW4z, zero_div]
      exact T.zero_mem
  -- the curve point
  have hcurve : ∀ k : Fin 5,
      Work.MotAS.kleinPAS (as2a D g) (as2b D g) (as2g D g) (as2c D g) k = 0 :=
    asY0_curve K D hD g
  have hc0 : as2c D g 0 = 1 := by
    show algebraMap ↥(twistFieldAS D g) (as2A D g) (asY0 D g 0) = 1
    have hy0 : asTwY D g 0 ≠ 0 := asTwY_zero_ne_zero D g hD.1
    have h1 : (asY0 D g 0 : OmA K D) = 1 := by
      change asTwY D g 0 / asTwY D g 0 = 1
      exact div_self hy0
    have h2 : asY0 D g 0 = 1 := Subtype.ext h1
    rw [h2, map_one]
  -- the ruling identity: `kleinRAS W` is proportional to the curve point
  have hrul : Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) (asW2 D g)
      = fun j => Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) (asW2 D g) 0
          * as2c D g j := by
    funext j
    have h := Work.MotAS.asRulingEval_gen h5R (as2a D g) (as2b D g) (as2g D g)
      (RatFunc.X : as2A D g) (as2c D g) hcurve 0 j
    rw [hc0, mul_one] at h
    exact h.symm
  -- the chart vector `v = W / W 0 = (1, φ 0, φ 1, φ 2, 0)`
  set v : Fin 5 → as2A D g :=
    ![1, asPhi2 D g 0, asPhi2 D g 1, asPhi2 D g 2, 0] with hvdef
  have hv : ∀ k : Fin 5, v k = asW2 D g k / asW2 D g 0 := by
    intro k
    rw [hvdef]
    fin_cases k
    · change (1 : as2A D g) = asW2 D g 0 / asW2 D g 0
      rw [div_self hW0ne]
    · change asPhi2 D g 0 = asW2 D g 1 / asW2 D g 0
      have h1 : Work.MotAS.asIdx (0 : Fin 3) = (1 : Fin 5) := Fin.ext rfl
      rw [← h1]
      rfl
    · change asPhi2 D g 1 = asW2 D g 2 / asW2 D g 0
      have h1 : Work.MotAS.asIdx (1 : Fin 3) = (2 : Fin 5) := Fin.ext rfl
      rw [← h1]
      rfl
    · change asPhi2 D g 2 = asW2 D g 3 / asW2 D g 0
      have h1 : Work.MotAS.asIdx (2 : Fin 3) = (3 : Fin 5) := Fin.ext rfl
      rw [← h1]
      rfl
    · change (0 : as2A D g) = asW2 D g 4 / asW2 D g 0
      rw [hW4z, zero_div]
  have hWv : asW2 D g = fun k => asW2 D g 0 * v k := by
    funext k
    rw [hv k, mul_div_cancel₀ _ hW0ne]
  have hvmem : ∀ k : Fin 5, v k ∈ T := by
    intro k
    rw [hv k]
    exact hpsi k
  have hPhi_mem : ∀ k : Fin 5,
      Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) v k ∈ T := fun k =>
    kleinRAS_mem T (as2a D g) (as2b D g) (as2g D g) v haT hbT hgT hvmem k
  have hsmul : Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) (asW2 D g)
      = fun k => (asW2 D g 0) ^ 3
          * Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) v k := by
    conv_lhs => rw [hWv]
    rw [Work.MotAS.kleinRAS_smul]
  -- `kleinRAS` does not vanish on the chart vector
  have hveq : (fun j => asW2 D g j / asW2 D g 0) = v := funext fun j => (hv j).symm
  have hPhi_ne : Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) v ≠ 0 := by
    have h := hrhon
    rw [hveq] at h
    exact h
  have hvlin : Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) v
      = fun j => Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) v 0 * as2c D g j := by
    funext j
    have h := congrFun hrul j
    rw [hsmul] at h
    have h2 : (asW2 D g 0) ^ 3 * Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) v j
        = ((asW2 D g 0) ^ 3
            * Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) v 0) * as2c D g j := h
    rw [mul_assoc] at h2
    exact mul_left_cancel₀ (pow_ne_zero 3 hW0ne) h2
  have hPhi0_ne : Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) v 0 ≠ 0 := by
    intro h0
    refine hPhi_ne ?_
    funext k
    simp only [congrFun hvlin k, h0, zero_mul, Pi.zero_apply]
  -- the coordinates of the curve point lie in `T`
  have hcT : ∀ i : Fin 5, as2c D g i ∈ T := by
    intro i
    have h := congrFun hvlin i
    have hdiv : as2c D g i
        = Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) v i
          / Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g) v 0 := by
      rw [eq_div_iff hPhi0_ne, mul_comm]
      exact h.symm
    rw [hdiv]
    exact T.div_mem (hPhi_mem i) (hPhi_mem 0)
  -- the ruling vectors at the curve point
  have hAq_mem : ∀ k : Fin 5,
      Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) k ∈ T := fun k =>
    asRuleQA_mem T (as2a D g) (as2b D g) (as2g D g) (as2c D g) haT hbT hgT hcT k
  have hBq_mem : ∀ k : Fin 5,
      Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) k ∈ T := fun k =>
    asRuleQB_mem T (as2a D g) (as2b D g) (as2g D g) (as2c D g) haT hbT hgT hcT k
  -- the rank minor, transported from the twist field to `as2A D g`
  have hrankA : Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1
        * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
      - Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
        * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1 ≠ 0 := by
    have hinj : Function.Injective
        (algebraMap ↥(twistFieldAS D g) (as2A D g)) := by
      rw [RatFunc.algebraMap_eq_C]
      exact RatFunc.C_injective
    have hmapA : ∀ i : Fin 5,
        (algebraMap ↥(twistFieldAS D g) (as2A D g))
            (Work.MotAS.asRuleQA (algebraMap 𝕜 ↥(twistFieldAS D g) D.a)
              (algebraMap 𝕜 ↥(twistFieldAS D g) D.b)
              (algebraMap K ↥(twistFieldAS D g) g)
              (asY0 D g) i)
          = Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) i := by
      intro i
      rw [Work.MotAS.map_asRuleQA]
      simp only [as2a, as2b, as2g]
      rw [IsScalarTower.algebraMap_apply 𝕜 ↥(twistFieldAS D g) (as2A D g) D.a,
        IsScalarTower.algebraMap_apply 𝕜 ↥(twistFieldAS D g) (as2A D g) D.b,
        IsScalarTower.algebraMap_apply K ↥(twistFieldAS D g) (as2A D g) g]
    have hmapB : ∀ i : Fin 5,
        (algebraMap ↥(twistFieldAS D g) (as2A D g))
            (Work.MotAS.asRuleQB (algebraMap 𝕜 ↥(twistFieldAS D g) D.a)
              (algebraMap 𝕜 ↥(twistFieldAS D g) D.b)
              (algebraMap K ↥(twistFieldAS D g) g)
              (asY0 D g) i)
          = Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) i := by
      intro i
      rw [Work.MotAS.map_asRuleQB]
      simp only [as2a, as2b, as2g]
      rw [IsScalarTower.algebraMap_apply 𝕜 ↥(twistFieldAS D g) (as2A D g) D.a,
        IsScalarTower.algebraMap_apply 𝕜 ↥(twistFieldAS D g) (as2A D g) D.b,
        IsScalarTower.algebraMap_apply K ↥(twistFieldAS D g) (as2A D g) g]
    intro h0
    apply hrank
    apply hinj
    simp only [map_sub, map_mul, map_zero]
    rw [hmapA 1, hmapB 0, hmapA 0, hmapB 1]
    exact h0
  -- the ruling parameter `RatFunc.X`
  have hf0 : asPhi2 D g 0 * asW2 D g 0 = asW2 D g 1 := by
    have h1 : Work.MotAS.asIdx (0 : Fin 3) = (1 : Fin 5) := Fin.ext rfl
    show asW2 D g (Work.MotAS.asIdx 0) / asW2 D g 0 * asW2 D g 0 = asW2 D g 1
    rw [h1, div_mul_cancel₀ _ hW0ne]
  have hXrel : (RatFunc.X : as2A D g)
        * (asPhi2 D g 0 * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g)
            (as2c D g) 0
          - Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1)
      = Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1
        - asPhi2 D g 0
          * Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0 := by
    have h : asPhi2 D g 0
          * (Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
            + (RatFunc.X : as2A D g)
              * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0)
        = Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1
          + (RatFunc.X : as2A D g)
            * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1 := by
      show asPhi2 D g 0 * asW2 D g 0 = asW2 D g 1
      exact hf0
    linear_combination (norm := refl_ring1) h
  have hden_ne : asPhi2 D g 0
        * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
      - Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1 ≠ 0 := by
    intro h0
    apply hrankA
    have h : asW2 D g 0 * (asPhi2 D g 0
            * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
          - Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1)
        = Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1
            * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
          - Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
            * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1 := by
      have hW0d : asW2 D g 0 = Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g)
            (as2c D g) 0
          + (RatFunc.X : as2A D g)
            * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0 := rfl
      have hW1d : asW2 D g 1 = Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g)
            (as2c D g) 1
          + (RatFunc.X : as2A D g)
            * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1 := rfl
      have hf : asW2 D g 0 * asPhi2 D g 0 = asW2 D g 1 := by
        rw [mul_comm]; exact hf0
      calc asW2 D g 0 * (asPhi2 D g 0
              * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
            - Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1)
          = asW2 D g 0 * asPhi2 D g 0
              * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
            - asW2 D g 0
              * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1 := by
              refl_ring1
        _ = asW2 D g 1 * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
            - asW2 D g 0
              * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1 := by
              rw [hf]
        _ = (Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1
              + (RatFunc.X : as2A D g)
                * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1)
              * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
            - (Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
              + (RatFunc.X : as2A D g)
                * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0)
              * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1 := by
              rw [hW1d, hW0d]
        _ = Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1
              * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
            - Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
              * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1 := by
              refl_ring1
    rw [h0, mul_zero] at h
    exact h.symm
  have hX : (RatFunc.X : as2A D g) ∈ T := by
    have hnum : Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1
          - asPhi2 D g 0
            * Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0 ∈ T :=
      T.sub_mem (hAq_mem 1) (T.mul_mem (hphi 0) (hAq_mem 0))
    have hdenmem : asPhi2 D g 0
          * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
        - Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1 ∈ T :=
      T.sub_mem (T.mul_mem (hphi 0) (hBq_mem 0)) (hBq_mem 1)
    have hXeq : (RatFunc.X : as2A D g)
        = (Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1
            - asPhi2 D g 0
              * Work.MotAS.asRuleQA (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0)
          / (asPhi2 D g 0
              * Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 0
            - Work.MotAS.asRuleQB (as2a D g) (as2b D g) (as2g D g) (as2c D g) 1) := by
      rw [eq_div_iff hden_ne]
      exact hXrel
    rw [hXeq]
    exact T.div_mem hnum hdenmem
  -- the image of the twist field lies in `T`
  have hSle : Subfield.closure (Set.range (algebraMap K (as2A D g))
      ∪ Set.range (as2c D g)) ≤ T := by
    rw [Subfield.closure_le]
    rintro x (hx | hx)
    · obtain ⟨k, rfl⟩ := hx
      exact hKm k
    · obtain ⟨i, rfl⟩ := hx
      exact hcT i
  have hsub : Set.range (algebraMap ↥(twistFieldAS D g) (as2A D g))
      ⊆ ↑(Subfield.closure (Set.range (algebraMap K (as2A D g))
          ∪ Set.range (as2c D g))) := by
    set F := twistFieldAS D g with hF
    set A := as2A D g with hA
    set ψ : Fin 5 → OmA K D := fun j => asTwY D g j / asTwY D g 0 with hψ
    set S : Subfield A := Subfield.closure (Set.range (algebraMap K A)
      ∪ Set.range (as2c D g)) with hS
    have aeval_mem : ∀ r : MvPolynomial (Set.range ψ) K,
        (MvPolynomial.aeval Subtype.val r : OmA K D) ∈ F := by
      intro r
      induction r using MvPolynomial.induction_on with
      | C k => rw [MvPolynomial.aeval_C]; exact F.algebraMap_mem k
      | add p q hp hq => rw [map_add]; exact F.add_mem hp hq
      | mul_X p i hp =>
        rw [map_mul, MvPolynomial.aeval_X]
        exact F.mul_mem hp (IntermediateField.subset_adjoin K _ i.2)
    have key : ∀ r : MvPolynomial (Set.range ψ) K,
        algebraMap ↥F A (⟨MvPolynomial.aeval Subtype.val r, aeval_mem r⟩ : ↥F) ∈ S := by
      intro r
      induction r using MvPolynomial.induction_on with
      | C k =>
        have h1 : (⟨MvPolynomial.aeval Subtype.val (MvPolynomial.C k), aeval_mem _⟩ : ↥F)
            = algebraMap K ↥F k := by
          refine Subtype.ext ?_
          show (MvPolynomial.aeval Subtype.val (MvPolynomial.C k) : OmA K D)
            = ↑(algebraMap K ↥F k)
          rw [MvPolynomial.aeval_C,
            IsScalarTower.algebraMap_apply K ↥F (OmA K D)]
          rfl
        rw [h1, ← IsScalarTower.algebraMap_apply K ↥F A]
        exact Subfield.subset_closure (Or.inl ⟨k, rfl⟩)
      | add p q hp hq =>
        have h1 : (⟨MvPolynomial.aeval Subtype.val (p + q), aeval_mem _⟩ : ↥F)
            = (⟨MvPolynomial.aeval Subtype.val p, aeval_mem p⟩ : ↥F)
              + ⟨MvPolynomial.aeval Subtype.val q, aeval_mem q⟩ := by
          apply Subtype.ext
          simp only [AddMemClass.coe_add, map_add]
        rw [h1, map_add]
        exact S.add_mem hp hq
      | mul_X p i hp =>
        have h1 : (⟨MvPolynomial.aeval Subtype.val (p * MvPolynomial.X i), aeval_mem _⟩ : ↥F)
            = (⟨MvPolynomial.aeval Subtype.val p, aeval_mem p⟩ : ↥F)
              * ⟨(i.1 : OmA K D),
                  IntermediateField.subset_adjoin K _ i.2⟩ := by
          apply Subtype.ext
          simp only [MulMemClass.coe_mul, map_mul, MvPolynomial.aeval_X]
        rw [h1, map_mul]
        refine S.mul_mem hp ?_
        obtain ⟨j, hj⟩ := i.2
        have h2 : (⟨(i.1 : OmA K D),
              IntermediateField.subset_adjoin K _ i.2⟩ : ↥F)
            = ⟨asY0 D g j,
                IntermediateField.subset_adjoin K _
                  (Set.mem_range_self j)⟩ := by
          apply Subtype.ext
          exact hj.symm
        rw [h2]
        exact Subfield.subset_closure (Or.inr ⟨j, rfl⟩)
    rintro y ⟨a, rfl⟩
    have ha : a.1 ∈ IntermediateField.adjoin K (Set.range ψ) := a.2
    rw [IntermediateField.mem_adjoin_iff] at ha
    obtain ⟨r, s, hrs⟩ := ha
    have ha_eq : a = (⟨MvPolynomial.aeval Subtype.val r, aeval_mem r⟩ : ↥F)
        / (⟨MvPolynomial.aeval Subtype.val s, aeval_mem s⟩ : ↥F) := by
      apply Subtype.ext
      show a.1 = _
      rw [hrs]
      rfl
    rw [ha_eq, map_div₀]
    exact S.div_mem (key r) (key s)
  have hFmem : ∀ a : ↥(twistFieldAS D g),
      algebraMap ↥(twistFieldAS D g) (as2A D g) a ∈ T := by
    intro a
    exact hSle (hsub ⟨a, rfl⟩)
  -- conclude
  have hle : IntermediateField.adjoin ↥(twistFieldAS D g)
        ({(RatFunc.X : as2A D g)} : Set (as2A D g)) ≤ T.toIntermediateField hFmem := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hX
  have htop : T.toIntermediateField hFmem = ⊤ := le_antisymm le_top (by
    rw [← RatFunc.adjoin_X (K := ↥(twistFieldAS D g))]
    exact hle)
  rw [eq_top_iff]
  intro x _
  exact (show x ∈ (T.toIntermediateField hFmem) from by rw [htop]; simp)

end Work.MotC5N3
