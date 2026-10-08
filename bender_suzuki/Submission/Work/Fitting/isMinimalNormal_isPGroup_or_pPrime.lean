import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.Fitting.pCoreSeries_mono

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.isMinimalNormal_isPGroup_or_pPrime`

A minimal normal subgroup `N` of a finite `p`-solvable group `G` is either a `p`-group
or a `p'`-group: `|N|` is a `p`-power or is coprime to `p`.

The proof runs along the upper `p`-series `1 = O_0(G) ≤ O_1(G) ≤ ... ≤ O_n(G) = G` whose
existence is `p`-solvability.  Let `i` be the least index with `N ≤ O_i(G)` (so `i ≥ 1`,
because `N ≠ ⊥`, and `j := i - 1` satisfies `N ≰ O_j(G)`).  The natural map
`N → G/O_j(G)` is injective by minimality of `N` (its kernel is the normal subgroup
`N ⊓ O_j(G) ≤ N`, which cannot be `N`, hence is `⊥`), and its image lies in
`O_π(G/O_j(G))` for `π = stepPi p j`, the `π`-core appearing in the definition of
`O_{j+1}(G)`.  Therefore `|N|` divides `|O_π(G/O_j(G))|`, which is a `π`-number by
`piCore_isPiNat`.  Since `π` is `(· = p)` for odd `j` and `(· ≠ p)` for even `j`,
this is the desired dichotomy.
-/

noncomputable section

open Classical

namespace Work.Fitting

theorem isMinimalNormal_isPGroup_or_pPrime (p : ℕ) (G : Type*) [Group G] [Finite G]
    [Work.Fitting.IsPSolvable p G] {N : Subgroup G} (h : Work.Fitting.IsMinimalNormal N) :
    Work.Fitting.IsPiNat (fun q => q = p) (Nat.card ↥N) ∨
      Work.Fitting.IsPiNat (fun q => q ≠ p) (Nat.card ↥N) := by
  classical
  obtain ⟨hNnorm, hNne, hNmin⟩ := h
  obtain ⟨n, hn⟩ := (inferInstance : IsPSolvable p G).out
  -- The set of indices `i` with `N ≤ O_i(G)` is nonempty, and `i` is its least element.
  have hex : ∃ i, N ≤ pCoreSeries p G i := ⟨n, by rw [hn]; exact le_top⟩
  set i := Nat.find hex with hi
  have hile : N ≤ pCoreSeries p G i := Nat.find_spec hex
  have hileast : ∀ m, N ≤ pCoreSeries p G m → i ≤ m := fun m hm => Nat.find_min' hex hm
  have hi0 : i ≠ 0 := by
    intro h0
    rw [h0, pCoreSeries_zero] at hile
    exact hNne (le_bot_iff.mp hile)
  set j := i - 1 with hjdef
  have hji : j + 1 = i := by rw [hjdef]; omega
  have hNj : ¬ N ≤ pCoreSeries p G j := by
    intro hle
    have h1 : i ≤ j := hileast j hle
    rw [hjdef] at h1
    omega
  have hNle_succ : N ≤ pCoreSeries p G (j + 1) := by rw [hji]; exact hile
  -- The natural map `N → G / O_j(G)`.
  let f : G →* G ⧸ pCoreSeries p G j := QuotientGroup.mk' (pCoreSeries p G j)
  let φ : ↥N →* G ⧸ pCoreSeries p G j := f.comp N.subtype
  -- Its kernel is `N ⊓ O_j(G)`, which is trivial by minimality of `N`.
  have hker : φ.ker = (N ⊓ pCoreSeries p G j).comap N.subtype := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_inf, φ, f,
      MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have hinf_bot : N ⊓ pCoreSeries p G j = ⊥ := by
    by_contra hne
    have hM := hNmin (N ⊓ pCoreSeries p G j) (inferInstance : (N ⊓ pCoreSeries p G j).Normal)
      inf_le_left hne
    exact hNj (hM ▸ inf_le_right)
  have hkerbot : φ.ker = (⊥ : Subgroup ↥N) := by
    rw [hker, hinf_bot, MonoidHom.comap_bot, Subgroup.ker_subtype]
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  -- The image of `φ` is contained in the `π`-core of the quotient.
  have hmem : ∀ x : ↥N, φ x ∈ piCore (fun q => if Even j then q ≠ p else q = p)
      (G ⧸ pCoreSeries p G j) := by
    intro x
    have hx : (x : G) ∈ pCoreSeries p G (j + 1) := hNle_succ x.2
    rw [pCoreSeries_succ] at hx
    exact hx
  have hrange_le : φ.range ≤ piCore (fun q => if Even j then q ≠ p else q = p)
      (G ⧸ pCoreSeries p G j) := by
    rintro y ⟨x, rfl⟩
    exact hmem x
  -- Hence `|N|` divides the order of a `π`-core, a `π`-number.
  have hcard : Nat.card ↥(φ.range) = Nat.card ↥N := by
    rw [← Subgroup.map_top φ, Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.topEquiv).toEquiv
  have hdvd : Nat.card ↥N ∣ Nat.card ↥(piCore (fun q => if Even j then q ≠ p else q = p)
      (G ⧸ pCoreSeries p G j)) := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hrange_le
  have hmain : IsPiNat (fun q => if Even j then q ≠ p else q = p) (Nat.card ↥N) :=
    isPiNat_of_dvd hdvd (piCore_isPiNat (G ⧸ pCoreSeries p G j)
      (fun q => if Even j then q ≠ p else q = p))
  -- Separate the two parities of `j`.
  by_cases hj : Even j
  · right
    have hπ : (fun q : ℕ => if Even j then q ≠ p else q = p) = fun q => q ≠ p := by
      funext q; simp [hj]
    rwa [hπ] at hmain
  · left
    have hπ : (fun q : ℕ => if Even j then q ≠ p else q = p) = fun q => q = p := by
      funext q; simp [hj]
    rwa [hπ] at hmain

end Work.Fitting
