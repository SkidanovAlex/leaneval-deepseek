import Mathlib
import Submission.Work.SSGRoute.free_lie_four_defs
import Submission.Work.SSGRoute.flg_defs
import Submission.Work.SSGRoute.flg_two_letters
import Submission.Work.SSGRoute.CC.FlgFourLetters
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SSGRoute.CC.freeLieFourFixedGeneration`

The residual generation statement: for a `σA`-fixed `v ∈ Wsub X` there is `w ∈ Wsub X` with
`v - (w + σA w) ∈ span{u * σA u + σA u * u : u ∈ Tsub X}`.

The proof decomposes `v` along the letter sets occurring in its support.  Writing `flg_proj T v`
for the projection onto the words whose letter set is exactly `T`:

* the sum over the *non*-`σ`-stable letter sets is `u₀ + σA u₀` for some `u₀ ∈ Wsub X`
  (`flg_odd_sum_delta`);
* for a `σ`-stable letter set `T` (which has even cardinality `≤ 4`, hence `2` or `4`), the piece
  `flg_proj T v` is `σA`-fixed, supported on words with letter set `T`, and is handled by the
  one-orbit lemma `flg_two_letters` (`|T| = 2`) or the two-orbit lemma `flg_four_letters`
  (`|T| = 4`).
-/

namespace Work.SSGRoute.CC

open scoped BigOperators

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The assembly of the target from the two finite cases. -/
theorem flg_assembly (X : Type) [Fintype X] [DecidableEq X] (σ : X ≃ X)
    (hσ : ∀ x, σ (σ x) = x) (hfree : ∀ x, σ x ≠ x)
    (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2]
      MonoidAlgebra (ZMod 2) (FreeMonoid X))
    (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
    (hgen : ∀ x, σA (MonoidAlgebra.single (FreeMonoid.of x) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ x)) 1)
    (two : ∀ x : X, σ x ≠ x → ∀ u : MonoidAlgebra (ZMod 2) (FreeMonoid X), u ∈ Wsub X → σA u = u →
      (∀ w : FreeMonoid X, u.coeff w ≠ 0 →
        (∀ y ∈ w.toList, y = x ∨ y = σ x) ∧ x ∈ w.toList ∧ σ x ∈ w.toList) →
      ∃ w ∈ Wsub X, u - (w + σA w) ∈ flgThetaSpan X σA)
    (four : ∀ a b c d : X, σ a = b → σ c = d → a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      ∀ u : MonoidAlgebra (ZMod 2) (FreeMonoid X), u ∈ Wsub X → σA u = u →
      (∀ w : FreeMonoid X, u.coeff w ≠ 0 →
        (∀ y ∈ w.toList, y = a ∨ y = b ∨ y = c ∨ y = d) ∧
        a ∈ w.toList ∧ b ∈ w.toList ∧ c ∈ w.toList ∧ d ∈ w.toList) →
      ∃ w ∈ Wsub X, u - (w + σA w) ∈ flgThetaSpan X σA) :
    ∀ v ∈ Wsub X, σA v = v →
      ∃ w ∈ Wsub X, v - (w + σA w) ∈ flgThetaSpan X σA := by
  classical
  intro v hv hfix
  -- the family of letter sets occurring in the support of `v`
  set 𝒯 : Finset (Finset X) := v.coeff.support.image (fun w => flg_letters w) with h𝒯
  have hmem𝒯 : ∀ w : FreeMonoid X, v.coeff w ≠ 0 → flg_letters w ∈ 𝒯 := by
    intro w hw
    rw [h𝒯]
    exact Finset.mem_image.mpr ⟨w, Finsupp.mem_support_iff.mpr hw, rfl⟩
  -- `𝒯` is `σ`-invariant
  have h𝒯inv : ∀ T ∈ 𝒯, T.image σ ∈ 𝒯 := by
    intro T hT
    obtain ⟨w, hw, hTw⟩ := Finset.mem_image.mp hT
    rw [Finsupp.mem_support_iff] at hw
    refine Finset.mem_image.mpr ⟨FreeMonoid.map (fun x => σ x) w, ?_, ?_⟩
    · rw [Finsupp.mem_support_iff]
      have hcoe : v.coeff (FreeMonoid.map (fun x => σ x) w) = v.coeff w := by
        have hc := flg_sigmaA_coeff σ σA hmul hone hgen v w
        rwa [hfix] at hc
      rw [hcoe]; exact hw
    · rw [flg_letters_map (fun x => σ x) w, hTw]
  -- the `σ`-stable and the non-`σ`-stable parts
  set p : Finset X → Prop := fun T => ∀ x ∈ T, σ x ∈ T with hp
  set sSt : Finset (Finset X) := 𝒯.filter p with hsSt
  set sOdd : Finset (Finset X) := 𝒯.filter (fun T => ¬ p T) with hsOdd
  have hsum : (∑ T ∈ 𝒯, flg_proj X T v) = v := flg_proj_sum v 𝒯 hmem𝒯
  have hsplit : (∑ T ∈ sOdd, flg_proj X T v) + (∑ T ∈ sSt, flg_proj X T v) = v := by
    conv_rhs => rw [← hsum]
    rw [hsSt, hsOdd, add_comm]
    exact Finset.sum_filter_add_sum_filter_not 𝒯 p (fun T => flg_proj X T v)
  -- the non-`σ`-stable part
  obtain ⟨u0, hu0mem, hu0eq⟩ :
      ∃ u ∈ Wsub X, (∑ T ∈ sOdd, flg_proj X T v) = u + σA u := by
    refine flg_odd_sum_delta σ hσ σA hmul hone hgen v hv hfix sOdd ?_ ?_
    · intro T hT
      have hT𝒯 : T ∈ 𝒯 := (Finset.mem_filter.mp hT).1
      have hTn : ¬ p T := (Finset.mem_filter.mp hT).2
      rw [hsOdd, Finset.mem_filter]
      refine ⟨h𝒯inv T hT𝒯, ?_⟩
      rw [hp] at hTn ⊢
      intro hc
      exact hTn (fun x hx => by
        have h1 : σ x ∈ T.image σ := Finset.mem_image_of_mem σ hx
        have hTeq : T.image σ = T := by
          have hsub : T ⊆ T.image σ := fun z hz => by
            have h1' : σ z ∈ T.image σ := Finset.mem_image_of_mem σ hz
            have h2 := hc (σ z) h1'
            rwa [hσ z] at h2
          exact (Finset.eq_of_subset_of_card_le hsub
            (le_of_eq (Finset.card_image_of_injective T σ.injective))).symm
        rw [← hTeq]; exact h1)
    · intro T hT
      exact (Finset.mem_filter.mp hT).2
  -- each `σ`-stable piece
  have hcard : ∀ T ∈ sSt, T.card = 2 ∨ T.card = 4 := by
    intro T hT
    have hT𝒯 : T ∈ 𝒯 := (Finset.mem_filter.mp hT).1
    have hTst : p T := (Finset.mem_filter.mp hT).2
    have hTst' : ∀ x ∈ T, σ x ∈ T := hTst
    obtain ⟨w, hw, hTw⟩ := Finset.mem_image.mp hT𝒯
    rw [Finsupp.mem_support_iff] at hw
    have hle : T.card ≤ 4 := by
      rw [← hTw]
      exact flg_Wsub_letters_le hv hw
    obtain ⟨t, ht⟩ := flg_Wsub_letters4 hv hw
    have hne : T ≠ ∅ := by rw [← hTw, ht]; exact flg_letters4_ne_empty t
    have hpos : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    have heven : Even T.card := flg_stable_card_even σ hσ hfree T hTst'
    obtain ⟨k, hk⟩ := heven
    omega
  have hpiece : ∀ T ∈ sSt, ∃ w ∈ Wsub X,
      flg_proj X T v - (w + σA w) ∈ flgThetaSpan X σA := by
    intro T hT
    have hTst : p T := (Finset.mem_filter.mp hT).2
    have hTst' : ∀ x ∈ T, σ x ∈ T := hTst
    have hvT : flg_proj X T v ∈ Wsub X := flg_proj_mem_Wsub T hv
    have hfixT : σA (flg_proj X T v) = flg_proj X T v := by
      rw [flg_sigmaA_proj_stable σ hσ σA hmul hone hgen hTst', hfix]
    have hsuppT : ∀ w : FreeMonoid X, (flg_proj X T v).coeff w ≠ 0 →
        (∀ y ∈ w.toList, y ∈ T) ∧ (∀ y ∈ T, y ∈ w.toList) := by
      intro w hw
      have h1 : flg_letters w = T := flg_proj_support T v hw
      constructor
      · intro y hy
        have : y ∈ flg_letters w := by simpa [flg_letters] using hy
        rwa [h1] at this
      · intro y hy
        have : y ∈ flg_letters w := by rw [h1]; exact hy
        simpa [flg_letters] using this
    rcases hcard T hT with h2 | h4
    · -- one `σ`-orbit
      obtain ⟨x, y, hxy, hTxy⟩ := Finset.card_eq_two.mp h2
      have hy : y = σ x := by
        have hmem : σ x ∈ ({x, y} : Finset X) := by
          rw [← hTxy]
          exact hTst' x (by rw [hTxy]; simp)
        rcases Finset.mem_insert.mp hmem with h | h
        · exact absurd h (hfree x)
        · exact (Finset.mem_singleton.mp h).symm
      have hTx : T = ({x, σ x} : Finset X) := by rw [hTxy, hy]
      have hsupp2 : ∀ w : FreeMonoid X, (flg_proj X T v).coeff w ≠ 0 →
          (∀ z ∈ w.toList, z = x ∨ z = σ x) ∧ x ∈ w.toList ∧ σ x ∈ w.toList := by
        intro w hw
        obtain ⟨h1, h2⟩ := hsuppT w hw
        refine ⟨fun z hz => ?_, h2 x (by rw [hTx]; simp), h2 (σ x) (by rw [hTx]; simp)⟩
        have hz' := h1 z hz
        rw [hTx] at hz'
        rcases Finset.mem_insert.mp hz' with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_singleton.mp h)
      exact two x (hfree x) (flg_proj X T v) hvT hfixT hsupp2
    · -- two `σ`-orbits
      have hpos : 0 < T.card := by rw [h4]; norm_num
      obtain ⟨x, hxT⟩ := Finset.card_pos.mp hpos
      have hsxT : σ x ∈ T := hTst' x hxT
      have hsxx : σ x ≠ x := hfree x
      have hssub : ({x, σ x} : Finset X) ⊂ T := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hxT
          · rw [Finset.mem_singleton.mp hz]; exact hsxT
        · intro hcon
          have hc := congrArg Finset.card hcon
          rw [Finset.card_pair hsxx.symm, h4] at hc
          norm_num at hc
      obtain ⟨y, hyT, hyne⟩ := Finset.exists_of_ssubset hssub
      rw [Finset.mem_insert, Finset.mem_singleton] at hyne
      have hyx : y ≠ x := fun h => hyne (Or.inl h)
      have hysx : y ≠ σ x := fun h => hyne (Or.inr h)
      have hsyT : σ y ∈ T := hTst' y hyT
      have hsyy : σ y ≠ y := hfree y
      have hxsy : x ≠ σ y := fun h => hysx (by rw [← hσ y, ← h])
      have hsxsy : σ x ≠ σ y := fun h => hyx (σ.injective h).symm
      have hcard4 : ({x, σ x, y, σ y} : Finset X).card = 4 :=
        Finset.card_eq_four.mpr ⟨x, σ x, y, σ y, hsxx.symm, hyx.symm, hxsy, hysx.symm,
          hsxsy, hsyy.symm, rfl⟩
      have hsub4 : ({x, σ x, y, σ y} : Finset X) ⊆ T := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact hxT
        · exact hsxT
        · exact hyT
        · exact hsyT
      have hTeq : T = ({x, σ x, y, σ y} : Finset X) :=
        (Finset.eq_of_subset_of_card_le hsub4 (by rw [hcard4, h4])).symm
      have hsupp4 : ∀ w : FreeMonoid X, (flg_proj X T v).coeff w ≠ 0 →
          (∀ z ∈ w.toList, z = x ∨ z = σ x ∨ z = y ∨ z = σ y) ∧
          x ∈ w.toList ∧ σ x ∈ w.toList ∧ y ∈ w.toList ∧ σ y ∈ w.toList := by
        intro w hw
        obtain ⟨h1, h2⟩ := hsuppT w hw
        refine ⟨fun z hz => ?_, h2 x (by rw [hTeq]; simp), h2 (σ x) (by rw [hTeq]; simp),
          h2 y (by rw [hTeq]; simp), h2 (σ y) (by rw [hTeq]; simp)⟩
        have hz' := h1 z hz
        rw [hTeq] at hz'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
        tauto
      exact four x (σ x) y (σ y) rfl rfl hsxx.symm hsyy.symm hyx.symm hxsy hysx.symm hsxsy
        (flg_proj X T v) hvT hfixT hsupp4
  let W : Finset X → MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
    fun T => if h : T ∈ sSt then Classical.choose (hpiece T h) else 0
  have hW1 : ∀ T (h : T ∈ sSt), W T ∈ Wsub X := by
    intro T h
    simp only [W, dif_pos h]
    exact (Classical.choose_spec (hpiece T h)).1
  have hW2 : ∀ T (h : T ∈ sSt),
      flg_proj X T v - (W T + σA (W T)) ∈ flgThetaSpan X σA := by
    intro T h
    simp only [W, dif_pos h]
    exact (Classical.choose_spec (hpiece T h)).2
  refine ⟨u0 + ∑ T ∈ sSt, W T, ?_, ?_⟩
  · exact Submodule.add_mem _ hu0mem (Submodule.sum_mem _ fun T hT => hW1 T hT)
  · have hres : v - ((u0 + ∑ T ∈ sSt, W T) + σA (u0 + ∑ T ∈ sSt, W T))
        = ∑ T ∈ sSt, (flg_proj X T v - (W T + σA (W T))) := by
      nth_rewrite 1 [hsplit.symm]
      rw [hu0eq, map_add, map_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      abel
    rw [hres]
    exact Submodule.sum_mem _ fun T hT => hW2 T hT


theorem freeLieFourFixedGeneration
    (X : Type) [Fintype X] (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x) (hfree : ∀ x, σ x ≠ x)
    (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2] MonoidAlgebra (ZMod 2) (FreeMonoid X))
    (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
    (hgen : ∀ x, σA (MonoidAlgebra.single (FreeMonoid.of x) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ x)) 1) :
    ∀ v ∈ Work.SSGRoute.Wsub X, σA v = v →
      ∃ w ∈ Work.SSGRoute.Wsub X,
        v - (w + σA w) ∈ Submodule.span (ZMod 2)
          (Set.range fun u : {u : MonoidAlgebra (ZMod 2) (FreeMonoid X) //
              u ∈ Work.SSGRoute.Tsub X} => (u : MonoidAlgebra (ZMod 2) (FreeMonoid X)) * σA u + σA u * u) := by
  classical
  exact flg_assembly X σ hσ hfree σA hmul hone hgen
    (fun x hx => flg_two_letters X x σ hσ hx σA hmul hone hgen)
    (fun a b c d ha hc hab hcd hac had hbc hbd =>
      flg_four_letters X σ hσ a b c d ha hc hab hcd hac had hbc hbd σA hmul hone hgen)

end Work.SSGRoute.CC
