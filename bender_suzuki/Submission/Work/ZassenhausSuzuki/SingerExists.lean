import Mathlib
import Submission.Work.ZassenhausSuzuki.SingerData
import Submission.Work.ZassenhausSuzuki.SzSetting
import Submission.Work.ZassenhausSuzuki.SingerTransport
import Submission.Work.ZassenhausSuzuki.SingerModelCycle.singer_cycle_model
import Submission.Work.ZassenhausSuzuki.Shadow.X5isoPSL2_of

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Existence of the Singer-cycle data inside `X5 H t`

This module supplies the transport half of Suzuki §8's Singer cycle: from

* `Work.ZassenhausSuzuki.Shadow.ChV12.X5isoPSL2_of` (`X5 H t ≅ PSL2Model n`, `|Q0sub H| = 2ⁿ`), and
* `SingerModelCycle.singer_cycle_model` (a cyclic self-centralising `V₀ ≤ PSL2Model n` of order
  `2ⁿ+1` with `|N(V₀)| = 2(2ⁿ+1)`, inverted by an involution, all of whose elements are strongly
  real), and
* `SingerTransport.singer_cycle_transport_full` (transport of that package along any isomorphism)

we obtain `SingerCycle.Data G H t`, i.e. the same package for a subgroup `V ≤ X5 H t` of the
ambient group, in the exact form consumed by `Work.ZassenhausSuzuki.singer_centralizer_eq` and
`Work.ZassenhausSuzuki.singer_conj_inf_eq_bot`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

/-- For an injective homomorphism `f : X →* Y`, the image of the normaliser of `H ≤ X` is the
normaliser of the image of `H`, intersected with the range of `f`. -/
theorem map_normalizer_eq_inf {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (H : Subgroup X) :
    (Subgroup.normalizer (H : Set X)).map f =
      Subgroup.normalizer ((H.map f : Subgroup Y) : Set Y) ⊓ f.range := by
  have hconj : ∀ x : X, (H.map f).map (↑(MulAut.conj (f x)) : Y →* Y)
      = (H.map (↑(MulAut.conj x) : X →* X)).map f := by
    intro x
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    show f x * f a * (f x)⁻¹ = f (x * a * x⁻¹)
    rw [map_mul, map_mul, map_inv]
  have hmapinj : Function.Injective (Subgroup.map f : Subgroup X → Subgroup Y) :=
    Subgroup.map_injective hf
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_inf.mpr ⟨?_, ⟨x, rfl⟩⟩
    have hxN : Subgroup.map (↑(MulAut.conj x) : X →* X) H = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hconj x]
    exact (hmapinj.eq_iff).mpr hxN
  · intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyN, ⟨x, rfl⟩⟩ := hy
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hyN ⊢
    rw [hconj x] at hyN
    exact (hmapinj.eq_iff).mp hyN

/-- The range of `Subgroup.subtype` is the subgroup itself. -/
theorem range_subtype_eq {G : Type} [Group G] (S : Subgroup G) :
    (Subgroup.subtype S).range = S := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- **Existence of the Singer-cycle data** (`SingerCycle.Data G H t`): from `SzHyp` and
`¬ IsAbelianSubgroup Q`, the group `X5 H t ≅ PSL2Model n` (`|Q0sub H| = 2ⁿ`) contains a cyclic
subgroup `V` of order `q + 1` (`q = |Q0sub H|`), self-centralising in `X5 H t`, with an involution
of `X5 H t` inverting it, and consisting of strongly real elements. -/
theorem exists_singer_cycle_data {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (h : SzHyp H Q t s) (hnab : ¬ IsAbelianSubgroup Q) :
    Nonempty (SingerCycle.Data G H t) := by
  classical
  obtain ⟨n, hn, hqcard, ⟨e⟩⟩ := Work.ZassenhausSuzuki.Shadow.ChV12.X5isoPSL2_of h
  obtain ⟨V₀, hcyc₀, hcard₀, hcent₀, hnorm₀, hinv₀, hsr₀⟩ :=
    SingerModelCycle.singer_cycle_model hn
  haveI : Finite ↥(Work.ThmF.Lemma5.X5 H t) := inferInstance
  obtain ⟨V, hcyc, hcard, hcent, hnorm, hinv, hsr⟩ :=
    singer_cycle_transport_full hcyc₀ hcard₀ hcent₀ hnorm₀ hinv₀ hsr₀ e
  let X5 : Subgroup G := Work.ThmF.Lemma5.X5 H t
  refine ⟨V.map (Subgroup.subtype X5), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `V ≤ X5 H t`
    intro a ha
    obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.mp ha
    exact v.2
  · -- `IsCyclic`
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective V (Subgroup.subtype X5)
      (Subgroup.subtype_injective X5))).mp hcyc
  · -- `|V| = q + 1`
    have h1 : Nat.card ↥(V.map (Subgroup.subtype X5)) = Nat.card ↥V :=
      Nat.card_congr (Subgroup.equivMapOfInjective V (Subgroup.subtype X5)
        (Subgroup.subtype_injective X5)).toEquiv.symm
    rw [h1, hcard, hqcard]
  · -- `C_{X5}(V) = V`
    intro x hxX hxcomm
    let y : ↥X5 := ⟨x, hxX⟩
    have hycent : y ∈ Subgroup.centralizer (V : Set ↥X5) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      apply Subtype.ext
      exact (hxcomm (v : G) (Subgroup.mem_map.mpr ⟨v, hv, rfl⟩)).symm
    have hyV : y ∈ V := by rw [← hcent]; exact hycent
    exact Subgroup.mem_map.mpr ⟨y, hyV, rfl⟩
  · -- `|N_{X5}(V)| = 2(q+1)`
    have hmap := map_normalizer_eq_inf (Subgroup.subtype X5) (Subgroup.subtype_injective X5) V
    rw [range_subtype_eq] at hmap
    have hcardN : Nat.card ↥(Subgroup.normalizer ((V.map (Subgroup.subtype X5) : Subgroup G) :
        Set G) ⊓ X5) = Nat.card ↥(Subgroup.normalizer (V : Set ↥X5)) := by
      rw [← hmap]
      exact Nat.card_congr (Subgroup.equivMapOfInjective
        (Subgroup.normalizer (V : Set ↥X5)) (Subgroup.subtype X5)
        (Subgroup.subtype_injective X5)).toEquiv.symm
    rw [hcardN, hnorm, hqcard]
  · -- an inverting involution
    obtain ⟨τ, hτ2, hτinv⟩ := hinv
    refine ⟨(τ : G), τ.2, ?_, ?_⟩
    · show (τ : G) * (τ : G) = 1
      rw [← Subgroup.coe_mul, hτ2, Subgroup.coe_one]
    · intro v hv
      obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hv
      have h1 : (τ : G) * v * (τ : G) = ((τ * w * τ : ↥X5) : G) := by
        rw [← hwv]
        simp
      rw [h1, hτinv w hw, ← hwv]
      simp
  · -- strong reality of the elements of `V`
    intro v hv
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hv
    obtain ⟨a, b, ha, hb, hab⟩ := hsr w hw
    exact ⟨(a : G), (b : G),
      by simpa using congrArg (fun u : ↥X5 => (u : G)) ha,
      by simpa using congrArg (fun u : ↥X5 => (u : G)) hb,
      by rw [← hwv]; simpa using congrArg (fun u : ↥X5 => (u : G)) hab⟩

end Work.ZassenhausSuzuki
