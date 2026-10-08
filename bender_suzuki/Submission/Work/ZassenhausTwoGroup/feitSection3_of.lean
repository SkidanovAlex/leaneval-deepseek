import Mathlib
import Submission.Work.ZassenhausTwoGroup.FeitThm2
import Submission.Work.ZassenhausTwoGroup.chi1_degree_eq
import Submission.Work.ZassenhausTwoGroup.etaStar_data
import Submission.Work.ZassenhausTwoGroup.zetaStar_norm
import Submission.Work.ZassenhausTwoGroup.brauerFowlerProp
import Submission.Work.ZassenhausTwoGroup.hchi_orb
import Submission.Work.ZassenhausTwoGroup.bf35_chars
import Submission.Work.ZassenhausTwoGroup.isNilpotent_Q
import Submission.Work.ZassenhausTwoGroup.fpf_on_Q
import Submission.Work.ZassenhausTwoGroup.even_card_Q
import Submission.Work.ZassenhausTwoGroup.isPGroup_two_iff
import Submission.Work.ZassenhausTwoGroup.oddPart_eq_bot_of_two_orbits
import Submission.Work.ZassenhausTwoGroup.count_le
import Submission.Work.ZassenhausTwoGroup.twoPoint_ne_bot
import Submission.Work.ZassenhausTwoGroup.commutator_HQ
import Submission.Work.ZassenhausTwoGroup.exists_half_transversal
import Submission.Work.ZassenhausTwoGroup.etaStar_family
import Submission.Work.ZassenhausTwoGroup.exists_zeta_ne_orbit
import Submission.Work.ZassenhausTwoGroup.exists_exceptional_orbit_deg
import Submission.Work.FeitSibley.Coherence.exists_nontrivial_linear_irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.feitSection3_of`

Feit's §3 of *On a class of doubly transitive permutation groups* (Illinois J. Math. **4** (1960)
170–186) derives the *displayed* character-theoretic conclusions (18)–(27) — recorded as
`FeitSection3Prop` — from Theorem 2 with its Corollaries 2.1 and 2.4 (`FeitThm2Prop`) in the
rank-one Zassenhaus set-up with `|D| ≠ |Q| - 1`.

This file supplies that derivation.  The three ingredients are:

* **Feit's proviso `|D| ≠ |Q| - 1`** (`twoPoint_ne_card_sub_one`): if `|D| = |Q| - 1` then
  `|Q| - 1 ≤ 1 · |D|`, i.e. `D` has at most *one* orbit on `Q#`; with `D` acting fixed point
  freely (`fpf_on_Q`), `Q` nilpotent (`isNilpotent_Q`, Thompson's theorem) and `|Q|` even
  (`even_card_Q`), the endgame `oddPart_eq_bot_of_two_orbits` forces `O_{2'}(Q) = ⊥`, i.e.
  `IsPGroup 2 Q` (`isPGroup_two_iff`), against the hypothesis.

* **The `η`-family** (`etaStar_family`): Feit's (18)/(19), i.e. `(|D|-1)/2` distinct irreducible
  characters of `G` of degree `|Q| + 1` with value `1` on `Q ∖ 1`.

* **Feit (27)** (`cfInner_mul_star_ne_zero`): the exceptional character `χ₁ = χ_{κ}` of degree
  `|D|` (`exists_exceptional_orbit_deg`, Feit (21)–(24)) is a constituent of `χ₁ ηᵢ^*`, via
  Corollary 2.1 applied to a second `Q`-character `ζ₂` inducing a different character
  (`exists_zeta_ne_orbit`) and the vanishing of `ηᵢ^* - 1` on the conjugates of `Q ∖ 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Classical
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-! ## 1. Feit's proviso `|D| ≠ |Q| - 1` for `Q` not a `2`-group -/

/-- **Feit's proviso.**  In the split rank-one Zassenhaus set-up with `Q` not a `2`-group one has
`|twoPoint H t| ≠ |Q| - 1` (the case `|D| = |Q| - 1` would give `|Q| - 1 ≤ 1 · |D|`, i.e. a
single `D`-orbit on `Q#`; with `D` acting fixed point freely, `Q` nilpotent and `|Q|` even the
endgame `oddPart_eq_bot_of_two_orbits` then forces `Q` to be a `2`-group). -/
theorem twoPoint_ne_card_sub_one {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    {H Q : Subgroup G} {t : G} (hTh : ThompsonFrobeniusProp)
    (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (hQ2 : ¬ IsPGroup 2 Q) :
    Nat.card (twoPoint H t) ≠ Nat.card Q - 1 := by
  intro heq
  have hnil : Group.IsNilpotent ↥Q := isNilpotent_Q hTh h hz (twoPoint_ne_bot h hz)
  have hnorm : twoPoint H t ≤ Subgroup.normalizer (Q : Set G) :=
    (twoPoint_le_H h).trans h.normal
  have hfp : IsFpfOn (twoPoint H t) Q := fpf_on_Q h hz
  have heven : Even (Nat.card Q) := even_card_Q h
  have hfew : FewOrbits (twoPoint H t) Q 1 := by
    unfold FewOrbits
    rw [heq]
    simp
  have hfew2 : FewOrbits (twoPoint H t) Q 2 := by
    unfold FewOrbits at hfew ⊢
    omega
  exact hQ2 ((isPGroup_two_iff hnil).mpr
    (oddPart_eq_bot_of_two_orbits hnil hnorm hfp heven hfew2))

/-! ## 2. Feit (27): the `ηᵢ^*` are constituents of `χ₁ χ̄₁` -/

/-- **Feit's (25)–(27).**  Let `χ₀` be the exceptional-character map of `FeitThm2Prop` (its
defining clauses `hχirr`, `hdiff`, `hvan` being the hypotheses), `κ` a non-trivial irreducible
character of `Q` with `χ₁ := χ₀ κ` irreducible, and `ζ₂` a non-trivial irreducible character of
`Q` inducing a *different* character of `G`.  Let `η ∈ Irr G` vanish on `Q ∖ 1` (as the induced
characters `ηᵢ^*` of Feit's (18) do).  Then `η` is a constituent of `χ₁ χ̄₁`.

The proof is Feit's: by Corollary 2.1 the difference `(ζ₂ 1) χ₁ - (κ 1) χ₀ζ₂` vanishes off the
conjugates of `Q ∖ 1`, while `η - 1` vanishes *on* them, so the pointwise product
`((ζ₂ 1) χ₁ - (κ 1) χ₀ζ₂)(η - 1)` is identically zero.  Taking the inner product with `χ₁`
gives `(ζ₂ 1)(⟪χ₁η, χ₁⟫ - 1) = (κ 1) ⟪χ₂η, χ₁⟫`, whose right hand side is a non-negative
integral multiple of `κ(1) > 0`; hence `⟪χ₁η, χ₁⟫ ≠ 0`, i.e. (conjugating) `⟪χ₁χ̄₁, η⟫ ≠ 0`. -/
theorem cfInner_mul_star_ne_zero {G : Type} [Group G] [Fintype G] {Q : Subgroup G}
    [Fintype ↥Q] {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {χ₀ : (↥Q → ℂ) → G → ℂ}
    (hχirr : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → χ₀ ζ ∈ Work.CharCore.Irr G)
    (hdiff : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' → ∀ g : G,
        (ζ' 1) * Work.Induction.indFun Q ζ g - (ζ 1) * Work.Induction.indFun Q ζ' g
          = (ε : ℂ) * ((ζ' 1) * χ₀ ζ g - (ζ 1) * χ₀ ζ' g))
    (hvan : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' → ∀ g : G,
        (¬ ∃ x : G, x * g * x⁻¹ ∈ Q ∧ x * g * x⁻¹ ≠ 1) →
          (ζ' 1) * χ₀ ζ g - (ζ 1) * χ₀ ζ' g = 0)
    {κ ζ₂ : ↥Q → ℂ} (hκ : κ ∈ Work.CharCore.Irr ↥Q) (hκ1 : κ ≠ 1)
    (hζ₂ : ζ₂ ∈ Work.CharCore.Irr ↥Q) (hζ₂1 : ζ₂ ≠ 1)
    (hInd : Work.Induction.indFun Q ζ₂ ≠ Work.Induction.indFun Q κ)
    {η : G → ℂ} (hη : η ∈ Work.CharCore.Irr G)
    (hηval : ∀ y : G, y ∈ Q → y ≠ 1 → η y = 1) :
    Work.CharCore.cfInner (χ₀ κ * fun g => star (χ₀ κ g)) η ≠ 0 := by
  classical
  have hχ₁ : χ₀ κ ∈ Work.CharCore.Irr G := hχirr κ hκ hκ1
  have hχ₂ : χ₀ ζ₂ ∈ Work.CharCore.Irr G := hχirr ζ₂ hζ₂ hζ₂1
  have hInd' : Work.Induction.indFun Q κ ≠ Work.Induction.indFun Q ζ₂ := hInd.symm
  have hεne : (ε : ℂ) ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hdeg₂ : (χ₀ ζ₂) 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hχ₂]
    exact_mod_cast Work.CharCore.irrDeg_ne_zero hχ₂
  have hz₂ne : (ζ₂ 1 : ℂ) ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hζ₂]
    exact_mod_cast Work.CharCore.irrDeg_ne_zero hζ₂
  have hκne : (κ 1 : ℂ) ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hκ]
    exact_mod_cast Work.CharCore.irrDeg_ne_zero hκ
  -- ## `χ₁ ≠ χ₂`
  have hne12 : χ₀ κ ≠ χ₀ ζ₂ := by
    intro heq
    have h1 : ∀ g : G, (ζ₂ 1) * Work.Induction.indFun Q κ g
        - (κ 1) * Work.Induction.indFun Q ζ₂ g
          = (ε : ℂ) * ((ζ₂ 1) - (κ 1)) * χ₀ ζ₂ g := by
      intro g
      have hh := hdiff κ hκ hκ1 ζ₂ hζ₂ hζ₂1 hInd' g
      rw [heq] at hh
      linear_combination hh
    have hzero : (ε : ℂ) * ((ζ₂ 1) - (κ 1)) * (χ₀ ζ₂) 1 = 0 := by
      have hh := h1 1
      rw [Work.Induction.indFun_apply_one, Work.Induction.indFun_apply_one] at hh
      have hann : (ζ₂ 1) * ((Q.index : ℂ) * (κ 1))
          - (κ 1) * ((Q.index : ℂ) * (ζ₂ 1)) = 0 := by
        ring
      rw [hann] at hh
      exact hh.symm
    have heqdeg : (ζ₂ 1 : ℂ) = (κ 1 : ℂ) := by
      rcases mul_eq_zero.mp hzero with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hεne
        · exact sub_eq_zero.mp h'
      · exact absurd h hdeg₂
    have hIndEq : Work.Induction.indFun Q κ = Work.Induction.indFun Q ζ₂ := by
      funext g
      have hh := h1 g
      rw [heqdeg] at hh
      have hh' : (κ 1) * (Work.Induction.indFun Q κ g
          - Work.Induction.indFun Q ζ₂ g) = 0 := by
        have hfac : (κ 1) * (Work.Induction.indFun Q κ g - Work.Induction.indFun Q ζ₂ g)
            = (κ 1) * Work.Induction.indFun Q κ g
              - (κ 1) * Work.Induction.indFun Q ζ₂ g := by ring
        rw [hfac, hh]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh').resolve_left hκne)
    exact hInd' hIndEq
  -- ## the pointwise vanishing of `((ζ₂ 1) χ₁ - (κ 1) χ₂) (η - 1)`
  have hFzero : (fun g : G => ((ζ₂ 1) * χ₀ κ g - (κ 1) * χ₀ ζ₂ g) * (η g - 1)) = 0 := by
    funext g
    by_cases hg : ∃ x : G, x * g * x⁻¹ ∈ Q ∧ x * g * x⁻¹ ≠ 1
    · obtain ⟨x, hxQ, hxne⟩ := hg
      have hcl : Work.CharCore.IsClassFun η := Work.CharCore.isClassFun_of_mem_Irr hη
      have hconj : x⁻¹ * (x * g * x⁻¹) * x = g := by group
      have hcl' : η (x⁻¹ * (x * g * x⁻¹) * x) = η (x * g * x⁻¹) := by
        simpa only [inv_inv] using hcl (x * g * x⁻¹) x⁻¹
      have hη1 : η g = 1 := by
        rw [← hconj, hcl']
        exact hηval (x * g * x⁻¹) hxQ hxne
      simp [hη1]
    · have h0 := hvan κ hκ hκ1 ζ₂ hζ₂ hζ₂1 hInd' g hg
      simp [h0]
  -- ## the inner product identity
  have hkey : (ζ₂ 1) * (Work.CharCore.cfInner (χ₀ κ * η) (χ₀ κ) - 1)
      - (κ 1) * Work.CharCore.cfInner (χ₀ ζ₂ * η) (χ₀ κ) = 0 := by
    have h0 : Work.CharCore.cfInner
        (fun g : G => ((ζ₂ 1) * χ₀ κ g - (κ 1) * χ₀ ζ₂ g) * (η g - 1)) (χ₀ κ) = 0 := by
      rw [hFzero]; simp [Work.CharCore.cfInner]
    have hpt : (fun g : G => ((ζ₂ 1) * χ₀ κ g - (κ 1) * χ₀ ζ₂ g) * (η g - 1))
        = (ζ₂ 1) • (χ₀ κ * η - χ₀ κ) - (κ 1) • (χ₀ ζ₂ * η - χ₀ ζ₂) := by
      funext g
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hpt, Work.CharCore.cfInner_sub_left, Work.CharCore.cfInner_smul_left,
      Work.CharCore.cfInner_smul_left, Work.CharCore.cfInner_sub_left,
      Work.CharCore.cfInner_sub_left,
      Work.CharCore.irr_orthonormal (χ₀ κ) (χ₀ κ) hχ₁ hχ₁,
      Work.CharCore.irr_orthonormal (χ₀ ζ₂) (χ₀ κ) hχ₂ hχ₁] at h0
    rw [if_pos rfl, if_neg (Ne.symm hne12)] at h0
    linear_combination h0
  -- ## `⟪χ₂η, χ₁⟫` is a natural number
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Work.CharCore.cfInner (χ₀ ζ₂ * η) (χ₀ κ) = (n : ℂ) := by
    have hchar : Work.CharCore.IsChar (χ₀ ζ₂ * η) :=
      Work.CharCore.isChar_mul (Work.CharCore.IsChar.of_mem_Irr hχ₂)
        (Work.CharCore.IsChar.of_mem_Irr hη)
    exact (Work.CharCore.isChar_iff hchar.isClassFun).mp hchar (χ₀ κ) hχ₁
  -- ## `⟪χ₁η, χ₁⟫ ≠ 0`
  have hA : Work.CharCore.cfInner (χ₀ κ * η) (χ₀ κ) ≠ 0 := by
    intro hA0
    have hcastζ : (ζ₂ 1 : ℂ) = ((Work.CharCore.irrDeg ζ₂ : ℝ) : ℂ) := by
      rw [Work.CharCore.irrDeg_spec hζ₂]; norm_num
    have hcastκ : (κ 1 : ℂ) = ((Work.CharCore.irrDeg κ : ℝ) : ℂ) := by
      rw [Work.CharCore.irrDeg_spec hκ]; norm_num
    have hz := hkey
    rw [hA0, hn, hcastζ, hcastκ] at hz
    have hreal : (Work.CharCore.irrDeg ζ₂ : ℝ) * ((0 : ℝ) - 1)
        - (Work.CharCore.irrDeg κ : ℝ) * (n : ℝ) = 0 := by
      have h2 : (((Work.CharCore.irrDeg ζ₂ : ℝ) * ((0 : ℝ) - 1)
          - (Work.CharCore.irrDeg κ : ℝ) * (n : ℝ) : ℝ) : ℂ) = 0 := by
        push_cast
        linear_combination hz
      exact_mod_cast h2
    have hpos : (0 : ℝ) < (Work.CharCore.irrDeg ζ₂ : ℝ) := by
      exact_mod_cast Work.CharCore.irrDeg_pos hζ₂
    have hpos' : (0 : ℝ) ≤ (Work.CharCore.irrDeg κ : ℝ) * (n : ℝ) := by positivity
    nlinarith [hreal, hpos, hpos']
  -- ## conjugation turns `⟪χ₁η, χ₁⟫` into `⟪χ₁χ̄₁, η⟫`
  have hconj : Work.CharCore.cfInner (χ₀ κ * fun g => star (χ₀ κ g)) η
      = starRingEnd ℂ (Work.CharCore.cfInner (χ₀ κ * η) (χ₀ κ)) := by
    simp only [Work.CharCore.cfInner, Pi.mul_apply, ← starRingEnd_apply]
    rw [map_mul, map_inv₀, map_natCast, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_mul, map_mul, Complex.conj_conj]
    ring
  rw [hconj]
  intro h
  exact hA (star_eq_zero.mp (by simpa only [starRingEnd_apply] using h))

end Work.ZassenhausTwoGroup

namespace Work.ZassenhausTwoGroup

theorem feitSection3_of (h2 : FeitThm2Prop) (hTh : ThompsonFrobeniusProp) :
    FeitSection3Prop := by
  intro G _ _ hsimple H Q t h hz hQ2
  classical
  have hQbot : Q ≠ ⊥ := by
    intro hb
    have h0 : Even (Nat.card (⊥ : Subgroup G)) := by rw [← hb]; exact even_card_Q h
    simp at h0
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQbot
  haveI : Group.IsNilpotent ↥Q := isNilpotent_Q hTh h hz (twoPoint_ne_bot h hz)
  have hne : Nat.card (twoPoint H t) ≠ Nat.card Q - 1 :=
    twoPoint_ne_card_sub_one hTh h hz hQ2
  -- a non-trivial linear character of `Q`
  obtain ⟨ζ₁, hζ₁Irr, hζ₁lin, hζ₁ne⟩ :=
    Work.FeitSibley.Coherence.exists_nontrivial_linear_irr ↥Q
  -- Feit's Theorem 2 with Corollaries 2.1 and 2.4
  obtain ⟨ε, hε, c, χ₀, hχirr, hdiff, hvan, hval, hconst⟩ := h2 G H Q t h hz hQ2 hne
  -- Feit's (21)–(24): an exceptional character of degree `|D|`
  obtain ⟨κ, hκ, hκ1, hκdeg⟩ :=
    exists_exceptional_orbit_deg H Q t h hz hQ2 hne hε hχirr hdiff hvan hval hconst
      hζ₁Irr hζ₁ne hζ₁lin
  -- a second `Q`-character inducing a different character of `G`
  obtain ⟨ζ₂, hζ₂, hζ₂1, hInd⟩ := exists_zeta_ne_orbit H Q t h hz hne hκ hκ1
  -- Feit's (18)/(19): the family `ηᵢ^*`
  obtain ⟨η, hηIrr, hηdeg, hηinj, hηval⟩ :=
    etaStar_family t h hz hQbot (commutator_HQ h hz)
  refine ⟨χ₀ κ, η, hχirr κ hκ hκ1, hκdeg, hηIrr, hηdeg, hηinj, ?_⟩
  intro i
  exact cfInner_mul_star_ne_zero hε hχirr hdiff hvan hκ hκ1 hζ₂ hζ₂1 hInd (hηIrr i) (hηval i)

end Work.ZassenhausTwoGroup
