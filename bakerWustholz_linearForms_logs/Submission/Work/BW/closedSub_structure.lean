import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.closedSubAux
import Submission.Work.BW.torus_coset_cover
import Submission.Work.BW.torus_basis_satLat
import Submission.Work.BW.torus_closed_subgroup
import Submission.Work.BW.closedSub_jordan

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# B2c: the structure of closed subgroups of `G = G_a × G_m^N`

`closedSub_structure` produces, for a Zariski-closed subgroup `H ≤ G`, a connected subgroup
`G' = G_a^ε × ker 𝒵` (with `𝒵 ⊆ ℤ^N` a *saturated* lattice, presented by its basis rows `M`) that
is contained in `H` with finite index: `H` is a finite union of `G'`-cosets.

Ingredients (each in its own module):
* `Work.BW.closedSub_jordan` (B2a): `H = G_a^ε × H_T`;
* `Work.BW.torus_closed_subgroup` (B2b), built on the character-independence lemma
  `Work.BW.char_sum_at_of_vanishing`: a closed subgroup of `0 × G_m^N` is the kernel of its
  character lattice;
* `Work.BW.torus_basis_satLat`: a basis `M` of the saturation of a character lattice;
* `Work.BW.torus_coset_cover`: the torus subgroup is covered by finitely many cosets of
  `ker (span M)`, with representatives inside the subgroup.
-/


namespace Work.BW

open MvPolynomial

/-! ## The torus part of a closed subgroup -/

/-- The torus part `H ∩ {y₀ = 0}` of `H`, read in the `N` torus coordinates. -/
private def torPart {N : ℕ} (H : Set (Fin (N + 1) → ℂ)) : Set (Fin N → ℂ) :=
  {t | Fin.cons (0 : ℂ) t ∈ H}

private theorem torPart_sub_Tor {N : ℕ} {H : Set (Fin (N + 1) → ℂ)} (hH : IsClosedSubG H) :
    torPart H ⊆ Tor N := by
  intro t ht i
  have h := (hH.1 (Fin.cons (0 : ℂ) t) ht) i
  simpa [torPart] using h

/-- `H ∩ {y₀ = 0}` is again a Zariski-closed subgroup. -/
private theorem inter_zero_isClosedSubG {N : ℕ} {H : Set (Fin (N + 1) → ℂ)}
    (hH : IsClosedSubG H) : IsClosedSubG {y : Fin (N + 1) → ℂ | y ∈ H ∧ y 0 = 0} := by
  obtain ⟨hInG, hgone, hmul, hinv, S, hS⟩ := hH
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy; exact hInG y hy.1
  · exact ⟨hgone, by simp [gone]⟩
  · intro a ha b hb
    refine ⟨hmul a ha.1 b hb.1, ?_⟩
    simp [gmul, ha.2, hb.2]
  · intro a ha
    refine ⟨hinv a ha.1, ?_⟩
    simp [ginv, ha.2]
  · refine ⟨insert (MvPolynomial.X (0 : Fin (N + 1))) S, ?_⟩
    rw [hS]
    ext y
    constructor
    · rintro ⟨⟨hinG, hvan⟩, hy0⟩
      refine ⟨hinG, ?_⟩
      intro f hf
      rcases hf with rfl | hf
      · simpa using hy0
      · exact hvan f hf
    · rintro ⟨hinG, hvan⟩
      refine ⟨⟨hinG, ?_⟩, ?_⟩
      · intro f hf; exact hvan f (Or.inr hf)
      · simpa using hvan (MvPolynomial.X (0 : Fin (N + 1))) (Or.inl rfl)

/-- B2b applied to the torus part: every torus point killed by the saturated character lattice of
`H ∩ {y₀ = 0}` lies in `H`. -/
private theorem mem_H_of_kerLat {N : ℕ} (H : Set (Fin (N + 1) → ℂ)) (hH : IsClosedSubG H)
    {k : Fin N → ℂ} (hk : k ∈ kerLat (satLat (charLat (torPart H)))) :
    Fin.cons (0 : ℂ) k ∈ H := by
  set H0 : Set (Fin (N + 1) → ℂ) := {y | y ∈ H ∧ y 0 = 0} with hH0def
  have hH0 : IsClosedSubG H0 := inter_zero_isClosedSubG hH
  have hH0z : ∀ y ∈ H0, y 0 = 0 := fun y hy => hy.2
  have hmain := torus_closed_subgroup H0 hH0 hH0z (Fin.cons (0 : ℂ) k)
    ((inG_cons_iff).mpr hk.1) (by simp) ?_
  · exact hmain.1
  · intro m hm
    have hmK : m ∈ charLat (torPart H) := by
      rw [mem_charLat_iff]
      intro y hy hym
      have hyH0 : Fin.cons (0 : ℂ) y ∈ H0 := ⟨hy, by simp⟩
      have h1 := hm (Fin.cons (0 : ℂ) y) hyH0
      simpa [torChar] using h1
    have hmSat : m ∈ satLat (charLat (torPart H)) := charLat_le_satLat _ hmK
    have h2 := hk.2 m hmSat
    simpa [torChar] using h2

/-- The character of a finite `ℤ`-linear combination. -/
private theorem torChar_sum {N : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (z : ι → Fin N → ℤ) {y : Fin N → ℂ} (hy : ∀ i, y i ≠ 0) :
    torChar (∑ j ∈ s, c j • z j) y = ∏ j ∈ s, (torChar (z j) y) ^ (c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [torChar_zero]
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.prod_insert has, torChar_add _ _ hy, ih,
        torChar_smul _ _ hy]

/-- B2c. Every closed subgroup `H` of `G` contains a connected `G' = G_a^ε × ker 𝒵` (`𝒵` saturated,
basis rows `M`) with finite index. Proof: B2a gives `H = G_a^ε × H_T`; B2b gives `H_T = ker 𝒵_H`
with `𝒵_H` the characters trivial on `H`; take `𝒵` the saturation (basis via
`Submodule.basisOfPid`), and `ker 𝒵_H / ker 𝒵 ↪ μ_e^ρ` (`e` the exponent of `𝒵/𝒵_H`) is finite.
Size 1.5–2.5k. -/
theorem closedSub_structure {N : ℕ} (H : Set (Fin (N + 1) → ℂ)) (hH : IsClosedSubG H) :
    ∃ (ε : Bool) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ), ρ ≤ N ∧ PrimSys M ∧ subSet N ρ ε M ⊆ H ∧
      ∃ F : Finset (Fin (N + 1) → ℂ), (↑F : Set (Fin (N + 1) → ℂ)) ⊆ H ∧
        H ⊆ ⋃ f ∈ F, gmul f '' subSet N ρ ε M := by
  classical
  obtain ⟨hInG, hgone, hmul, hinv, S, hS⟩ := hH
  have hHc : IsClosedSubG H := ⟨hInG, hgone, hmul, hinv, S, hS⟩
  -- the torus part of `H` is a torus subgroup
  have hKTor : torPart H ⊆ Tor N := torPart_sub_Tor hHc
  -- basis of the saturated character lattice
  obtain ⟨ρ, M, hρ, hPrim, hspan⟩ := torus_basis_satLat (torPart H)
  have hM_sat : ∀ j, M j ∈ satLat (charLat (torPart H)) := by
    intro j
    rw [← hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  -- `ε = true` exactly when some element of `H` has nonzero `G_a` coordinate
  set ε : Bool := (if (∃ a ∈ H, a 0 ≠ 0) then true else false) with hεdef
  have hε_true : ε = true → ∃ a ∈ H, a 0 ≠ 0 := by
    intro h
    by_contra hc
    have h2 : ε = false := by rw [hεdef, if_neg hc]
    rw [h2] at h
    exact Bool.noConfusion h
  have hε_false : ε = false → ∀ a ∈ H, a 0 = 0 := by
    intro h a ha
    by_contra hc
    have hex : ∃ a ∈ H, a 0 ≠ 0 := ⟨a, ha, hc⟩
    have h2 : ε = true := by rw [hεdef, if_pos hex]
    rw [h2] at h
    exact Bool.noConfusion h
  have hker_sub : ∀ k ∈ kerLat (satLat (charLat (torPart H))), Fin.cons (0 : ℂ) k ∈ H :=
    fun k hk => mem_H_of_kerLat H hHc hk
  -- `subSet ⊆ H`
  have hsub : subSet N ρ ε M ⊆ H := by
    intro y hy
    obtain ⟨hyε, hyne, hyM⟩ := hy
    have hker : (fun i : Fin N => y i.succ) ∈ kerLat (satLat (charLat (torPart H))) := by
      refine ⟨fun i => hyne i, ?_⟩
      intro z hz
      rw [← hspan] at hz
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hz
      rw [← hc, torChar_sum Finset.univ c M (fun i => hyne i)]
      refine Finset.prod_eq_one (fun j _ => ?_)
      have hMj : torChar (M j) (fun i : Fin N => y i.succ) = 1 := by
        simpa [torChar] using hyM j
      rw [hMj, one_zpow]
    have hkH : Fin.cons (0 : ℂ) (fun i : Fin N => y i.succ) ∈ H := hker_sub _ hker
    rcases Bool.eq_false_or_eq_true ε with hε | hε
    · obtain ⟨a, ha, ha0⟩ := hε_true hε
      have hga := (closedSub_jordan H hHc a ha).2 ha0 (y 0)
      have hprod := hmul _ hga _ hkH
      have he : gmul (Fin.cons (y 0) (fun _ : Fin N => (1 : ℂ)))
          (Fin.cons (0 : ℂ) (fun i : Fin N => y i.succ)) = y := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [gmul]
        · intro j; simp [gmul]
      rwa [he] at hprod
    · have hy0 : y 0 = 0 := hyε hε
      have he : y = Fin.cons (0 : ℂ) (fun i : Fin N => y i.succ) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simpa using hy0
        · intro j; simp
      rw [he]; exact hkH
  -- the finite coset cover
  obtain ⟨F0, hF0K, hF0⟩ := torus_coset_cover (torPart H) hKTor ρ M hM_sat
  refine ⟨ε, ρ, M, hρ, hPrim, hsub, F0.image (fun t => Fin.cons (0 : ℂ) t), ?_, ?_⟩
  · intro y hy
    rw [Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact hF0K ht
  · intro y hy
    have hyk : (fun i : Fin N => y i.succ) ∈ torPart H := (closedSub_jordan H hHc y hy).1
    have hykne : ∀ i : Fin N, y i.succ ≠ 0 := hKTor hyk
    obtain ⟨f, hfF, hfker⟩ := hF0 (fun i : Fin N => y i.succ) hyk
    set z : Fin (N + 1) → ℂ :=
      Fin.cons (y 0) (tmul (tInv f) (fun i : Fin N => y i.succ)) with hzdef
    refine Set.mem_iUnion₂.mpr ⟨Fin.cons (0 : ℂ) f, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨f, hfF, rfl⟩
    · rw [Set.mem_image]
      refine ⟨z, ?_, ?_⟩
      · -- `z ∈ subSet`
        refine ⟨?_, ?_, ?_⟩
        · intro hε
          rw [hzdef]; simp only [Fin.cons_zero]
          exact hε_false hε y hy
        · intro i
          rw [hzdef]; simp only [Fin.cons_succ, tmul, tInv]
          exact mul_ne_zero (inv_ne_zero (hKTor (hF0K hfF) i)) (hykne i)
        · intro j
          rw [hzdef]; simp only [Fin.cons_succ]
          have h1 : torChar (M j) (tmul (tInv f) (fun i : Fin N => y i.succ)) = 1 :=
            hfker.2 (M j) (Submodule.subset_span ⟨j, rfl⟩)
          simpa only [torChar] using h1
      · -- `gmul (cons 0 f) z = y`
        rw [hzdef]
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [gmul]
        · intro j
          simp only [gmul, Fin.cons_zero, Fin.cons_succ, tmul, tInv]
          exact mul_inv_cancel_left₀ (hKTor (hF0K hfF) j) (y j.succ)

end Work.BW
