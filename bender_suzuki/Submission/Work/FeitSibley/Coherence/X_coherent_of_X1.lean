import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.exists_indQH_of_mem_scriptSR_le_Q
import Submission.Work.FeitSibley.Coherence.commutator_le_of_chief
import Submission.Work.FeitSibley.Coherence.two_mul_card_D_add_one_le_card_of_odd
import Submission.Work.FeitSibley.Coherence.coherent_union_singleton
import Submission.Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr
import Submission.Work.FeitSibley.GroupTheory.exists_maximal_normal_below
import Submission.Work.FeitSibley.Coherence.engine
import Submission.Work.FeitSibley.Coherence.deg_sq_le_of_mem_scriptSR_center
import Submission.Work.FeitSibley.Coherence.SubFSZ_aux
import Submission.Work.Clifford.gallagher_ind_eq
import Submission.Work.CharCore.irr_degree_dvd_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.X_coherent_of_X1`

Peterfalvi II, Appendice XII, step (3): the passage from coherence of
`𝒳₁ = 𝒳 ∩ 𝒮(S') = 𝒮(S') ∖ 𝒮(S'Z)` to coherence of `𝒳 = 𝒮 ∖ 𝒮(Z)`, where
`Z = FSZ h = [Q₁,Q₁] ∩ Z(Q₁)`, `S' = [S,S]`.

The proof follows Isaacs 7.22 / the source: since `Q₁` is a `p`-group, the degrees of the
irreducible characters of `Q₁` are powers of `p`, so the element

`ξ = Ind_Q^H (1_S ⊗ θ₁)`,   `θ₁ ∈ Irr Q₁` of *minimal* degree among those with `Z ⊄ ker θ₁`,

has degree `|D| · θ₁(1)` dividing `χ(1)` for every `χ ∈ 𝒳` (all degrees in `𝒳` are
`|D| · deg λ · deg θ` with `deg θ₁ | deg θ`).  Adjoining the elements of `𝒳 ∖ 𝒳₁` to `𝒳₁` one at
a time with Feit's criterion (`coherent_of_feit_step`) it therefore suffices to prove the strict
inequality `2 · ξ(1) · χ(1) < ∑_{ψ ∈ 𝒳 ∩ 𝒮(γ k)} ψ(1)²`, which follows from

* `∑_{ψ ∈ 𝒮(γ k)∖𝒮(γ k ⊔ Z)} ψ(1)² = |D| · [S : γ k] · (|Q₁| - [Q₁ : Z])`
  (`sum_deg_sq_scriptSR_sdiff_gen`),
* `ξ(1)² ≤ |D|² · |Q₁| / |Z(Q₁)|` and `χ(1)² ≤ |D|² · [S : γ k] · |Q₁| / |Z(Q₁)|`
  (Isaacs 2.30, `deg_sq_le_of_mem_scriptSR_center`),
* `[S : γ k] ≥ 2` (as `γ k ≤ S' < S`) and `|Z| ≥ 2|D| + 1`
  (`two_mul_card_D_add_one_le_card_of_odd`),

the numerical bookkeeping being `numeric_step3`.
-/

namespace Work.FeitSibley.Coherence

set_option maxHeartbeats 1000000

open Classical

noncomputable section

variable {G : Type} [Group G] [Fintype G]

/-! ## `Z = FSZ h` is nontrivial for a nonabelian `p`-group `Q₁` -/

/-- In a nilpotent group `X`, `[X,X] ∩ Z(X) ≠ 1` as long as `[X,X] ≠ 1`: the last nontrivial
term of the lower central series is contained in both `[X,X]` and `Z(X)`. -/
private theorem commutator_inf_center_ne_bot {X : Type*} [Group X] (hX : Group.IsNilpotent X)
    (hX' : commutator X ≠ ⊥) : commutator X ⊓ Subgroup.center X ≠ ⊥ := by
  haveI : Group.IsNilpotent ↥(⊤ : Subgroup X) := Group.isNilpotent_top.mpr hX
  have hex : ∃ m, (⊤ : Subgroup X).lowerCentralSeries m = ⊥ :=
    (Subgroup.isNilpotent_iff_lowerCentralSeries (⊤ : Subgroup X)).mp ‹_›
  have hspec : (⊤ : Subgroup X).lowerCentralSeries (Nat.find hex) = ⊥ := Nat.find_spec hex
  have htop_ne : (⊤ : Subgroup X) ≠ ⊥ := by
    intro htop
    exact hX' (eq_bot_iff.mpr (by rw [← htop]; exact le_top))
  have hNpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h, Subgroup.lowerCentralSeries_zero] at hspec
      exact absurd hspec htop_ne
    · exact h
  have hN2 : 2 ≤ Nat.find hex := by
    by_contra hcon
    have hle : Nat.find hex = 0 ∨ Nat.find hex = 1 := by omega
    rcases hle with h | h
    · rw [h, Subgroup.lowerCentralSeries_zero] at hspec
      exact absurd hspec htop_ne
    · rw [h, Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero,
          Subgroup.commutator_comm] at hspec
      exact hX' hspec
  have hprev : (⊤ : Subgroup X).lowerCentralSeries (Nat.find hex - 1) ≠ ⊥ := by
    intro hc
    exact Nat.find_min hex (by omega) hc
  have hstep : ⁅(⊤ : Subgroup X).lowerCentralSeries (Nat.find hex - 1), (⊤ : Subgroup X)⁆ = ⊥ := by
    have h1 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [← Subgroup.lowerCentralSeries_succ, h1, hspec]
  have hcen : (⊤ : Subgroup X).lowerCentralSeries (Nat.find hex - 1) ≤ Subgroup.center X := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hstep
    exact Subgroup.mem_centralizer_iff.mp (hle hz) g (Subgroup.mem_top g)
  have hle' : (⊤ : Subgroup X).lowerCentralSeries (Nat.find hex - 1) ≤ commutator X := by
    have hmono := Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup X)
      (by omega : 1 ≤ Nat.find hex - 1)
    rwa [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero,
      Subgroup.commutator_comm] at hmono
  intro hc
  refine hprev (le_bot_iff.mp ?_)
  exact (le_inf hle' hcen).trans (le_of_eq hc)

/-- `FSZ h = ⁅Q₁,Q₁⁆ ⊓ C_G(Q₁) = [Q₁,Q₁] ∩ Z(Q₁)` is nontrivial when `↥Q₁` is a nonabelian
`p`-group (`hab` says `⁅Q₁,Q₁⁆ ≠ ⊥`). -/
theorem FSZ_ne_bot (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime)
    (hpg : IsPGroup p h.Q1) (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥) : FSZ h ≠ ⊥ := by
  intro hbot
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Group.IsNilpotent ↥h.Q1 := hpg.isNilpotent
  have hcomm : commutator ↥h.Q1 ≠ ⊥ := by
    intro hc
    apply hab
    have hmap := Subgroup.map_subtype_commutator h.Q1
    rw [← hmap, hc, Subgroup.map_bot]
  have hne := commutator_inf_center_ne_bot (X := ↥h.Q1) ‹Group.IsNilpotent ↥h.Q1› hcomm
  apply hne
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have hx1' : (x : G) ∈ ⁅h.Q1, h.Q1⁆ := by
    have hmap := Subgroup.map_subtype_commutator h.Q1
    rw [← hmap]
    exact ⟨x, hx1, rfl⟩
  have hx2' : (x : G) ∈ Subgroup.centralizer (h.Q1 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h2 := Subgroup.mem_center_iff.mp hx2 ⟨q, hq⟩
    exact congrArg Subtype.val h2
  have hmem : (x : G) ∈ FSZ h := Subgroup.mem_inf.mpr ⟨hx1', hx2'⟩
  rw [hbot] at hmem
  exact Subtype.ext (Subgroup.mem_bot.mp hmem)

/-! ## Elementary manipulations of the finsets `𝒮(R)` -/

/-- If `χ ∈ 𝒮` is trivial on `R` and on `Z` (with `R, Z ≤ H`), then it is trivial on `R ⊔ Z`:
the level set of an irreducible character is a subgroup. -/
theorem le_ker_sup_of_mem_scriptS (h : Work.FeitSibley.FSData G) {R Z : Subgroup G}
    (hRH : R ≤ h.H) (hZH : Z ≤ h.H) {χ : ↥h.H → ℂ}
    (hχS : χ ∈ Work.FeitSibley.scriptS h.H h.Q1)
    (hR : ∀ x : ↥h.H, (x : G) ∈ R → χ x = χ 1)
    (hZ : ∀ x : ↥h.H, (x : G) ∈ Z → χ x = χ 1) :
    ∀ x : ↥h.H, (x : G) ∈ R ⊔ Z → χ x = χ 1 := by
  classical
  have hχ : χ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hχS).1
  obtain ⟨K, _, hKeq⟩ := Work.CharCore.charKernel_subgroup hχ
  have hRle : R ≤ K.map h.H.subtype := by
    intro g hg
    refine Subgroup.mem_map.mpr ⟨⟨g, hRH hg⟩, ?_, rfl⟩
    have h2 : (⟨g, hRH hg⟩ : ↥h.H) ∈ Work.CharCore.charKernel χ := hR ⟨g, hRH hg⟩ hg
    rwa [← hKeq] at h2
  have hZle : Z ≤ K.map h.H.subtype := by
    intro g hg
    refine Subgroup.mem_map.mpr ⟨⟨g, hZH hg⟩, ?_, rfl⟩
    have h2 : (⟨g, hZH hg⟩ : ↥h.H) ∈ Work.CharCore.charKernel χ := hZ ⟨g, hZH hg⟩ hg
    rwa [← hKeq] at h2
  have hsup : R ⊔ Z ≤ K.map h.H.subtype := sup_le hRle hZle
  intro x hx
  obtain ⟨k, hkK, hk⟩ := Subgroup.mem_map.mp (hsup hx)
  have hkx : k = x := Subtype.ext hk
  have h3 : k ∈ Work.CharCore.charKernel χ := hKeq ▸ hkK
  rw [← hkx]
  exact h3

/-- `𝒮(R) ∩ 𝒮(Z) = 𝒮(R ⊔ Z)`. -/
theorem scriptSR_inter_eq (h : Work.FeitSibley.FSData G) {R Z : Subgroup G} (hRH : R ≤ h.H)
    (hZH : Z ≤ h.H) :
    Work.FeitSibley.scriptSR h.H h.Q1 R ∩ Work.FeitSibley.scriptSR h.H h.Q1 Z
      = Work.FeitSibley.scriptSR h.H h.Q1 (R ⊔ Z) := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · intro χ hχ
    obtain ⟨hχR, hχZ⟩ := Finset.mem_inter.mp hχ
    obtain ⟨hχS, hRk⟩ := (mem_scriptSR_iff h R).mp hχR
    obtain ⟨-, hZk⟩ := (mem_scriptSR_iff h Z).mp hχZ
    exact (mem_scriptSR_iff h (R ⊔ Z)).mpr
      ⟨hχS, le_ker_sup_of_mem_scriptS h hRH hZH hχS hRk hZk⟩
  · intro χ hχ
    obtain ⟨hχS, hk⟩ := (mem_scriptSR_iff h (R ⊔ Z)).mp hχ
    exact Finset.mem_inter.mpr
      ⟨(mem_scriptSR_iff h R).mpr ⟨hχS, fun x hx => hk x (Subgroup.mem_sup_left hx)⟩,
       (mem_scriptSR_iff h Z).mpr ⟨hχS, fun x hx => hk x (Subgroup.mem_sup_right hx)⟩⟩

/-- `(𝒮 ∖ 𝒮(Z)) ∩ 𝒮(R) = 𝒮(R) ∖ 𝒮(R ⊔ Z)`: the `Z`-nontrivial part of `𝒮(R)`. -/
theorem sdiff_FSZ_inter_scriptSR (h : Work.FeitSibley.FSData G) {R : Subgroup G}
    (hRH : R ≤ h.H) :
    (Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h))
        ∩ Work.FeitSibley.scriptSR h.H h.Q1 R
      = Work.FeitSibley.scriptSR h.H h.Q1 R
        \ Work.FeitSibley.scriptSR h.H h.Q1 (R ⊔ FSZ h) := by
  classical
  have hZle : FSZ h ≤ h.H := (FSZ_le_Q1 h).trans (h.Q1_le_H)
  ext χ
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hχS, hχZ⟩, hχR⟩
    refine ⟨hχR, fun hcon => hχZ ?_⟩
    obtain ⟨-, hk⟩ := (mem_scriptSR_iff h (R ⊔ FSZ h)).mp hcon
    exact (mem_scriptSR_iff h (FSZ h)).mpr
      ⟨scriptSR_subset_scriptS h R hχR, fun x hx => hk x (Subgroup.mem_sup_right hx)⟩
  · rintro ⟨hχR, hχnot⟩
    refine ⟨⟨scriptSR_subset_scriptS h R hχR, fun hcon => hχnot ?_⟩, hχR⟩
    obtain ⟨hχS, hZk⟩ := (mem_scriptSR_iff h (FSZ h)).mp hcon
    exact (mem_scriptSR_iff h (R ⊔ FSZ h)).mpr
      ⟨hχS, le_ker_sup_of_mem_scriptS h hRH hZle hχS
        (fun x hx => ((mem_scriptSR_iff h R).mp hχR).2 x hx) hZk⟩

/-! ## Degrees of irreducible characters of `Q₁` are powers of `p`, and a minimal `θ₁` -/

/-- The degree of an irreducible character of a `p`-group is a power of `p`. -/
theorem irrDeg_eq_pow_of_isPGroup (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime)
    (hpg : IsPGroup p h.Q1) {θ : ↥h.Q1 → ℂ} (hθ : θ ∈ Work.CharCore.Irr ↥h.Q1) :
    ∃ j : ℕ, Work.CharCore.irrDeg θ = p ^ j := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥h.Q1)).mp hpg
  have hdvd : Work.CharCore.irrDeg θ ∣ p ^ n := by
    rw [← hn]
    exact Work.CharCore.irr_degree_dvd_card hθ
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨k, hk⟩

/-- There is an irreducible character `θ` of `Q₁` which is nontrivial on `Z = FSZ h ≠ ⊥` and
whose degree is minimal among all such. -/
theorem exists_irr_min_deg_not_triv_on_FSZ (h : Work.FeitSibley.FSData G)
    (hFSZ : FSZ h ≠ ⊥) :
    ∃ θ ∈ Work.CharCore.Irr ↥h.Q1,
      (∃ z : ↥h.Q1, (z : G) ∈ FSZ h ∧ θ z ≠ θ 1) ∧
      ∀ θ' ∈ Work.CharCore.Irr ↥h.Q1,
        (∃ z' : ↥h.Q1, (z' : G) ∈ FSZ h ∧ θ' z' ≠ θ' 1) →
        Work.CharCore.irrDeg θ ≤ Work.CharCore.irrDeg θ' := by
  classical
  -- an element `z ≠ 1` of `Z = FSZ h`
  have hlt : (⊥ : Subgroup G) < FSZ h := lt_of_le_of_ne bot_le (fun hc => hFSZ hc.symm)
  obtain ⟨z, hzZ, hz1⟩ := SetLike.exists_of_lt hlt
  have hzQ1 : z ∈ h.Q1 := FSZ_le_Q1 h hzZ
  set z₀ : ↥h.Q1 := ⟨z, hzQ1⟩ with hz₀def
  have hz₀ne : z₀ ≠ 1 := by
    intro hcon
    exact hz1 (congrArg Subtype.val hcon)
  -- some `θ ∈ Irr Q₁` with `θ z₀ ≠ θ 1`
  have hex : ∃ θ ∈ Work.CharCore.Irr ↥h.Q1, θ z₀ ≠ θ 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 := Work.Clifford.sum_irr_deg_mul_apply_ne_one (H := ↥h.Q1) hz₀ne
    have h2 : (∑ β ∈ Work.CharCore.Irr ↥h.Q1, (β 1) * β z₀)
        = (Nat.card ↥h.Q1 : ℂ) := by
      rw [Finset.sum_congr rfl (fun β hβ => by rw [hcon β hβ])]
      simpa [pow_two] using (Work.CharCore.sum_irr_degree_sq (G := ↥h.Q1))
    rw [h2] at h1
    exact (Nat.cast_ne_zero.mpr (Nat.card_pos (α := ↥h.Q1)).ne') h1
  -- minimality
  obtain ⟨θ₀, hθ₀Irr, hθ₀ne⟩ := hex
  have hexP : ∃ n : ℕ, ∃ θ ∈ Work.CharCore.Irr ↥h.Q1,
      (∃ z : ↥h.Q1, (z : G) ∈ FSZ h ∧ θ z ≠ θ 1) ∧ Work.CharCore.irrDeg θ = n :=
    ⟨_, θ₀, hθ₀Irr, ⟨z₀, hzZ, hθ₀ne⟩, rfl⟩
  obtain ⟨θ, hθIrr, hθne, hθdeg⟩ := Nat.find_spec hexP
  refine ⟨θ, hθIrr, hθne, fun θ' hθ'Irr hθ'ne => ?_⟩
  have := Nat.find_min' hexP ⟨θ', hθ'Irr, hθ'ne, rfl⟩
  rwa [← hθdeg] at this

end

/-! ## The divisor `ξ = Ind_Q^H (1_S ⊗ θ₁)` -/

/-- `ξ = Ind_Q^H (1_S ⊗ θ₁) ∈ 𝒮 ∖ 𝒮(Z)` whenever `θ₁` is nontrivial on `Z = FSZ h`. -/
theorem xi_mem_sdiff_FSZ {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {θ₁ : ↥h.Q1 → ℂ}
    (hθ₁ : θ₁ ∈ Work.CharCore.Irr ↥h.Q1)
    (hntriv : ∃ z : ↥h.Q1, (z : G) ∈ FSZ h ∧ θ₁ z ≠ θ₁ 1) :
    h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)
      ∈ Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h) := by
  classical
  have hθ₁ne : θ₁ ≠ fun _ : ↥h.Q1 => (1 : ℂ) := by
    obtain ⟨z, -, hz⟩ := hntriv
    intro hcon
    exact hz (by rw [hcon])
  have hξS : h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)
      ∈ Work.FeitSibley.scriptS h.H h.Q1 := by
    refine (Work.FeitSibley.CharQ.scriptS_eq_image h).mpr
      ⟨h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁,
        Work.FeitSibley.CharQ.prodChar_mem_Irr h Work.CharCore.principalChar_mem_Irr hθ₁,
        ?_, rfl⟩
    obtain ⟨z, -, hz⟩ := hntriv
    refine ⟨⟨(z : G), h.Q1_le_Q z.2⟩, z.2, fun hcon => hz ?_⟩
    rw [Work.FeitSibley.CharQ.prodChar_apply_of_mem_Q1 h _ θ₁ ⟨(z : G), h.Q1_le_Q z.2⟩ z.2,
      Work.FeitSibley.FSData.prodChar_one] at hcon
    simpa using hcon
  refine Finset.mem_sdiff.mpr ⟨hξS, fun hcon => ?_⟩
  obtain ⟨z, hz, hzne⟩ := hntriv
  exact hzne ((mem_scriptSR_prodChar_iff h Work.CharCore.principalChar_mem_Irr hθ₁ hθ₁ne
    (FSZ_le_Q1 h) (FSZ_normal h)).mp hcon z hz)

/-- `ξ = Ind_Q^H (1_S ⊗ θ₁)` is trivial on `S' = [S,S]`: it is induced from a character of `Q`
which is trivial on `S'`. -/
theorem xi_mem_scriptSR_FSScomm {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {θ₁ : ↥h.Q1 → ℂ}
    (hθ₁ : θ₁ ∈ Work.CharCore.Irr ↥h.Q1)
    (hntriv : ∃ z : ↥h.Q1, (z : G) ∈ FSZ h ∧ θ₁ z ≠ θ₁ 1) :
    h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)
      ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) := by
  classical
  have hξS := (Finset.mem_sdiff.mp (xi_mem_sdiff_FSZ h hθ₁ hntriv)).1
  have htriv : ∀ y : ↥h.Q, (y : G) ∈ FSScomm h →
      h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁ y
        = h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁ 1 := by
    intro y hy
    rw [Work.FeitSibley.Coherence.prodChar_apply_of_mem_S h _ θ₁ y (FSScomm_le_S h hy),
      Work.FeitSibley.FSData.prodChar_one]
  refine (mem_scriptSR_iff h (FSScomm h)).mpr ⟨hξS, fun x hx => ?_⟩
  exact indQH_apply_eq_one_of_triv_on_Z h ((FSScomm_le_S h).trans h.S_le_Q)
    (H_le_normalizer_FSScomm h) htriv hx

/-- **The divisor.**  For `θ₁ ∈ Irr Q₁` of minimal degree among the irreducible characters of
`Q₁` which are nontrivial on `Z = FSZ h`, the degree of `ξ = Ind_Q^H (1_S ⊗ θ₁)` divides the
degree of every `χ ∈ 𝒳 = 𝒮 ∖ 𝒮(Z)`.

Indeed `χ = Ind_Q^H (prodChar λ θ)` with `θ ∈ Irr Q₁` nontrivial on `Z`, so
`deg θ₁ ∣ deg θ` (both are powers of `p` and `deg θ₁ ≤ deg θ`), while
`deg χ = |D| · deg λ · deg θ` and `deg ξ = |D| · deg θ₁`. -/
theorem xi_dvd_irrDeg {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {p : ℕ} (hp : p.Prime)
    (hpg : IsPGroup p h.Q1) {θ₁ : ↥h.Q1 → ℂ} (hθ₁ : θ₁ ∈ Work.CharCore.Irr ↥h.Q1)
    (hntriv : ∃ z : ↥h.Q1, (z : G) ∈ FSZ h ∧ θ₁ z ≠ θ₁ 1)
    (hmin : ∀ θ' ∈ Work.CharCore.Irr ↥h.Q1,
      (∃ z' : ↥h.Q1, (z' : G) ∈ FSZ h ∧ θ' z' ≠ θ' 1) →
        Work.CharCore.irrDeg θ₁ ≤ Work.CharCore.irrDeg θ') :
    ∀ χ ∈ Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h),
      Work.CharCore.irrDeg (h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁))
        ∣ Work.CharCore.irrDeg χ := by
  classical
  intro χ hχ
  obtain ⟨hχS, hχnotZ⟩ := Finset.mem_sdiff.mp hχ
  obtain ⟨φ, hφIrr, ⟨x₀, hx₀Q1, hx₀ne⟩, hχeq⟩ :=
    (Work.FeitSibley.CharQ.scriptS_eq_image h).mp hχS
  obtain ⟨lam, hlam, θ, hθ, hφeq⟩ :=
    Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr h hφIrr
  -- `θ ≠ 1` (as `Q₁ ⊄ ker φ`) and `θ` nontrivial on `Z` (as `χ ∉ 𝒮(Z)`)
  have hθne : θ ≠ fun _ : ↥h.Q1 => (1 : ℂ) := by
    intro hcon
    have h2 := (Work.FeitSibley.CharQ.prodChar_Q1_kernel_iff h hlam hθ).mpr hcon x₀ hx₀Q1
    rw [hφeq] at hx₀ne
    exact hx₀ne h2
  have hθZ : ∃ z : ↥h.Q1, (z : G) ∈ FSZ h ∧ θ z ≠ θ 1 := by
    by_contra hcon
    push_neg at hcon
    refine hχnotZ ?_
    rw [hχeq, hφeq]
    exact (mem_scriptSR_prodChar_iff h hlam hθ hθne (FSZ_le_Q1 h) (FSZ_normal h)).mpr hcon
  -- divisibility of the `θ`-degrees
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥h.Q1)).mp hpg
  have ha : Work.CharCore.irrDeg θ₁ ∣ p ^ n := by
    rw [← hn]; exact Work.CharCore.irr_degree_dvd_card hθ₁
  have hb : Work.CharCore.irrDeg θ ∣ p ^ n := by
    rw [← hn]; exact Work.CharCore.irr_degree_dvd_card hθ
  have hdpow : Work.CharCore.irrDeg θ₁ ∣ Work.CharCore.irrDeg θ :=
    dvd_of_le_of_dvd_prime_pow hp ha hb (hmin θ hθ hθZ)
  -- the degrees of `χ` and of `ξ`
  have hχIrr : χ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hχS).1
  have hξIrr : h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)
      ∈ Work.CharCore.Irr ↥h.H :=
    (Finset.mem_filter.mp ((Finset.mem_sdiff.mp (xi_mem_sdiff_FSZ h hθ₁ hntriv)).1)).1
  have hχ1 : χ 1 = (Nat.card h.D : ℂ) * (φ 1) := by
    rw [hχeq, Work.FeitSibley.CharQ.indQH_eq_indFun]
    change Work.Induction.indFun (h.Q.subgroupOf h.H) (Work.FeitSibley.CharQ.pull h φ) 1
      = (Nat.card h.D : ℂ) * (φ 1)
    rw [Work.Induction.indFun_apply_one, Work.FeitSibley.CharQ.pull_one, index_subgroupOf_Q h]
  have hφdeg : Work.CharCore.irrDeg φ
      = Work.CharCore.irrDeg lam * Work.CharCore.irrDeg θ := by
    have hφirr' : h.prodChar lam θ ∈ Work.CharCore.Irr ↥h.Q := hφeq ▸ hφIrr
    refine Nat.cast_injective (R := ℂ) ?_
    rw [Nat.cast_mul, hφeq, ← Work.CharCore.irrDeg_spec hφirr',
      Work.FeitSibley.FSData.prodChar_one, ← Work.CharCore.irrDeg_spec hlam,
      ← Work.CharCore.irrDeg_spec hθ]
  have hχdeg : Work.CharCore.irrDeg χ
      = Nat.card h.D * (Work.CharCore.irrDeg lam * Work.CharCore.irrDeg θ) := by
    refine Nat.cast_injective (R := ℂ) ?_
    rw [Nat.cast_mul, Nat.cast_mul, ← Work.CharCore.irrDeg_spec hχIrr, hχ1,
      Work.CharCore.irrDeg_spec hφIrr, hφdeg, Nat.cast_mul]
  have hξ1 : (h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)) 1
      = (Nat.card h.D : ℂ) * (θ₁ 1) := by
    rw [Work.FeitSibley.CharQ.indQH_eq_indFun]
    change Work.Induction.indFun (h.Q.subgroupOf h.H)
      (Work.FeitSibley.CharQ.pull h (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)) 1
      = (Nat.card h.D : ℂ) * (θ₁ 1)
    rw [Work.Induction.indFun_apply_one, Work.FeitSibley.CharQ.pull_one,
      Work.FeitSibley.FSData.prodChar_one, index_subgroupOf_Q h]
    ring
  have hξdeg : Work.CharCore.irrDeg (h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁))
      = Nat.card h.D * Work.CharCore.irrDeg θ₁ := by
    refine Nat.cast_injective (R := ℂ) ?_
    rw [Nat.cast_mul, ← Work.CharCore.irrDeg_spec hξIrr,
      ← Work.CharCore.irrDeg_spec hθ₁, hξ1]
  rw [hξdeg, hχdeg]
  exact Nat.mul_dvd_mul_left _ (hdpow.trans (dvd_mul_left _ _))

/-- The numerical contradiction of the Feit step. -/
private theorem numeric_step3 {d I Z p q A x y : ℝ}
    (hd : 0 < d) (hI : 2 ≤ I) (hZge : 2 * d + 1 ≤ Z) (hp : 0 < p) (hpq : p ≤ q)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hAx : A ≤ 2 * x * y)
    (hx2 : x ^ 2 ≤ d ^ 2 * p) (hy2 : y ^ 2 ≤ d ^ 2 * I * p)
    (hA : d * I * q * (Z - 1) ≤ A) : False := by
  have hZ1 : (0 : ℝ) ≤ Z - 1 := by linarith
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hdIq : (0 : ℝ) ≤ d * I * q * (Z - 1) := by positivity
  have hle : d * I * q * (Z - 1) ≤ 2 * x * y := le_trans hA hAx
  have hxy : (0 : ℝ) ≤ 2 * x * y := by positivity
  have hsq : (d * I * q * (Z - 1)) ^ 2 ≤ (2 * x * y) ^ 2 := pow_le_pow_left₀ hdIq hle 2
  have h1 : x ^ 2 * y ^ 2 ≤ (d ^ 2 * p) * y ^ 2 := mul_le_mul_of_nonneg_right hx2 (sq_nonneg y)
  have h2 : (d ^ 2 * p) * y ^ 2 ≤ d ^ 4 * I * p ^ 2 := by nlinarith [hy2]
  have h3 : (2 * x * y) ^ 2 ≤ 4 * (d ^ 4 * I * p ^ 2) := by nlinarith [h1, h2]
  have h4 : d ^ 2 * I ^ 2 * q ^ 2 * (Z - 1) ^ 2 ≤ 4 * (d ^ 4 * I * p ^ 2) := by
    nlinarith [hsq, h3]
  have h5 : (d ^ 2 * I) * (I * q ^ 2 * (Z - 1) ^ 2) ≤ (d ^ 2 * I) * (4 * d ^ 2 * p ^ 2) := by
    nlinarith [h4]
  have h6 : I * q ^ 2 * (Z - 1) ^ 2 ≤ 4 * d ^ 2 * p ^ 2 :=
    le_of_mul_le_mul_left h5 (by positivity)
  have h7 : 4 * d ^ 2 * p ^ 2 ≤ 4 * d ^ 2 * q ^ 2 := by
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hp) hpq 2) (by positivity : (0:ℝ) ≤ 4 * d ^ 2)
    linarith [this]
  have h8 : I * (Z - 1) ^ 2 * q ^ 2 ≤ 4 * d ^ 2 * q ^ 2 := by nlinarith [h6, h7]
  have h9 : I * (Z - 1) ^ 2 ≤ 4 * d ^ 2 := le_of_mul_le_mul_right h8 (by positivity)
  nlinarith [h9, hI, hZge, hd]

/-- Monotonicity of the cardinality of subgroups. -/
private theorem card_le_card_of_le {G : Type} [Group G] [Fintype G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card ↥H ≤ Nat.card ↥K :=
  Nat.card_le_card_of_injective (Subgroup.inclusion h) (fun a b hab =>
    Subtype.ext (by simpa using congrArg (fun x : ↥K => (x : G)) hab))

theorem X_coherent_of_X1 {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (hD : h.D ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpg : IsPGroup p h.Q1)
    (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥)
    (hcoh : Work.Coherence.Coherent
      (Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSScomm h) \
        Work.FeitSibley.scriptSR h.H h.Q1
          (Work.FeitSibley.Coherence.FSScomm h ⊔ Work.FeitSibley.Coherence.FSZ h))
      (Work.FeitSibley.indLin h.H)) :
    Work.Coherence.Coherent
      (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSZ h))
      (Work.FeitSibley.indLin h.H) := by
  classical
  have hFSZ : FSZ h ≠ ⊥ := FSZ_ne_bot h hp hpg hab
  have hZleQ1 : FSZ h ≤ h.Q1 := FSZ_le_Q1 h
  have hZleH : FSZ h ≤ h.H := hZleQ1.trans h.Q1_le_H
  have hZn : h.H ≤ Subgroup.normalizer (FSZ h : Set G) := FSZ_normal h
  obtain ⟨θ₁, hθ₁, hntriv, hmin⟩ := exists_irr_min_deg_not_triv_on_FSZ h hFSZ
  have hξdvd := xi_dvd_irrDeg h hp hpg hθ₁ hntriv hmin
  have hξSR := xi_mem_scriptSR_FSScomm h hθ₁ hntriv
  have hξdiff := xi_mem_sdiff_FSZ h hθ₁ hntriv
  by_cases hS'bot : FSScomm h = ⊥
  · rw [hS'bot, bot_sup_eq, scriptSR_bot h] at hcoh
    exact hcoh
  · -- `S' ≠ ⊥`: run the lower central series of `S` from `S'` down to `⊥`
    haveI : Group.IsNilpotent ↥h.S := h.S_nilpotent
    have hSne : h.S ≠ ⊥ := by
      intro hbot
      apply hS'bot
      show ⁅h.S, h.S⁆ = ⊥
      rw [hbot]
      simp
    have hSlt : FSScomm h < h.S := commutator_lt_self_of_ne_bot h.S hSne
    let γ : ℕ → Subgroup G := fun i => (h.S).lowerCentralSeries i
    have hγ1 : γ 1 = FSScomm h := by
      show (h.S).lowerCentralSeries 1 = Work.FeitSibley.Coherence.FSScomm h
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
    have hγsucc : ∀ k, γ (k+1) = ⁅γ k, h.S⁆ := fun k => by
      show (h.S).lowerCentralSeries (k+1) = ⁅(h.S).lowerCentralSeries k, h.S⁆
      rw [Subgroup.lowerCentralSeries_succ]
    have hγleS : ∀ i, γ i ≤ h.S := fun i => by
      have h := Subgroup.lowerCentralSeries_antitone h.S (Nat.zero_le i)
      rwa [Subgroup.lowerCentralSeries_zero] at h
    have hγleH : ∀ i, γ i ≤ h.H := fun i => (hγleS i).trans (h.S_le_Q.trans h.Q_le_H)
    have hγanti : ∀ k, γ (k+1) ≤ γ k := fun k =>
      Subgroup.lowerCentralSeries_antitone h.S (Nat.le_succ k)
    have hγHn : ∀ i, h.H ≤ Subgroup.normalizer (((γ i) : Subgroup G) : Set G) := fun i =>
      H_le_normalizer_lowerCentralSeries h i
    obtain ⟨m, hm⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries h.S).mp h.S_nilpotent
    have hbase : Work.Coherence.Coherent
        (Work.FeitSibley.scriptSR h.H h.Q1 (γ 1) \
          Work.FeitSibley.scriptSR h.H h.Q1 (γ 1 ⊔ FSZ h))
        (Work.FeitSibley.indLin h.H) := by
      rw [hγ1]; exact hcoh
    have step : ∀ k, 1 ≤ k →
        Work.Coherence.Coherent
          (Work.FeitSibley.scriptSR h.H h.Q1 (γ k) \
            Work.FeitSibley.scriptSR h.H h.Q1 (γ k ⊔ FSZ h))
          (Work.FeitSibley.indLin h.H) →
        Work.Coherence.Coherent
          (Work.FeitSibley.scriptSR h.H h.Q1 (γ (k+1)) \
            Work.FeitSibley.scriptSR h.H h.Q1 (γ (k+1) ⊔ FSZ h))
          (Work.FeitSibley.indLin h.H) := by
      intro k hk ih
      have hγkS' : γ k ≤ FSScomm h := by
        have hh : γ k ≤ γ 1 := by
          show (h.S).lowerCentralSeries k ≤ (h.S).lowerCentralSeries 1
          exact Subgroup.lowerCentralSeries_antitone h.S hk
        rwa [hγ1] at hh
      -- `ξ ∈ 𝒮(γ k) ∖ 𝒮(γ k ⊔ Z)`
      have hξS0 : h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)
          ∈ Work.FeitSibley.scriptSR h.H h.Q1 (γ k) \
            Work.FeitSibley.scriptSR h.H h.Q1 (γ k ⊔ FSZ h) := by
        refine Finset.mem_sdiff.mpr ⟨scriptSR_subset_of_le h hγkS' hξSR, fun hcon => ?_⟩
        exact (Finset.mem_sdiff.mp hξdiff).2
          (scriptSR_subset_of_le h (le_sup_right : FSZ h ≤ γ k ⊔ FSZ h) hcon)
      refine coherent_of_feit_step
        (S0 := Work.FeitSibley.scriptSR h.H h.Q1 (γ k) \
          Work.FeitSibley.scriptSR h.H h.Q1 (γ k ⊔ FSZ h))
        (S := Work.FeitSibley.scriptSR h.H h.Q1 (γ (k+1)) \
          Work.FeitSibley.scriptSR h.H h.Q1 (γ (k+1) ⊔ FSZ h))
        (τ := Work.FeitSibley.indLin h.H) ?_ ?_ ?_ ?_ ih ?_
      · -- `S₀ ⊆ S`
        intro χ hχ
        rw [← sdiff_FSZ_inter_scriptSR h (hγleH k)] at hχ
        rw [← sdiff_FSZ_inter_scriptSR h (hγleH (k+1))]
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hχ).1,
          scriptSR_subset_of_le h (hγanti k) (Finset.mem_inter.mp hχ).2⟩
      · -- irreducible
        intro χ hχ
        exact (Finset.mem_filter.mp (scriptSR_subset_scriptS h _
          (Finset.mem_sdiff.mp hχ).1)).1
      · -- `Ind_H^G` is an isometry on `𝒮`
        exact (Work.FeitSibley.CharQ.isometry_indLin h).mono
          (fun χ hχ => scriptSR_subset_scriptS h _ (Finset.mem_sdiff.mp hχ).1)
      · -- virtual characters on `ℤ[S₀]⁰`
        intro α hα
        exact isVChar_indLin_zSpan0_scriptS h
          (Work.Coherence.zSpan0_mono
            (fun χ hχ => scriptSR_subset_scriptS h _ (Finset.mem_sdiff.mp hχ).1) hα)
      · -- the Feit obstruction cannot occur
        intro χ hχS hχS0 hall
        have hχSR : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (γ (k+1)) := (Finset.mem_sdiff.mp hχS).1
        have hχSscript : χ ∈ Work.FeitSibley.scriptS h.H h.Q1 := scriptSR_subset_scriptS h _ hχSR
        have hχnot : χ ∉ Work.FeitSibley.scriptSR h.H h.Q1 (γ (k+1) ⊔ FSZ h) :=
          (Finset.mem_sdiff.mp hχS).2
        have hχKer : ∀ x : ↥h.H, (x : G) ∈ γ (k+1) → χ x = χ 1 :=
          ((mem_scriptSR_iff h (γ (k+1))).mp hχSR).2
        -- `χ ∈ 𝒳 = 𝒮 ∖ 𝒮(Z)`
        have hχX : χ ∈ Work.FeitSibley.scriptS h.H h.Q1 \
            Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h) := by
          refine Finset.mem_sdiff.mpr ⟨hχSscript, fun hcon => hχnot ?_⟩
          obtain ⟨-, hZk⟩ := (mem_scriptSR_iff h (FSZ h)).mp hcon
          exact (mem_scriptSR_iff h (γ (k+1) ⊔ FSZ h)).mpr
            ⟨hχSscript, le_ker_sup_of_mem_scriptS h (hγleH (k+1)) hZleH hχSscript
              hχKer hZk⟩
        have hdvd := hξdvd χ hχX
        have hχIrr : χ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hχSscript).1
        have hξIrr : h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)
            ∈ Work.CharCore.Irr ↥h.H :=
          (Finset.mem_filter.mp ((Finset.mem_sdiff.mp hξdiff).1)).1
        have hdeg : χ 1 = ((Work.CharCore.irrDeg χ /
            Work.CharCore.irrDeg (h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)) : ℕ) : ℂ)
            * (h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)) 1 := by
          rw [Work.CharCore.irrDeg_spec hχIrr, Work.CharCore.irrDeg_spec hξIrr, ← Nat.cast_mul,
            Nat.div_mul_cancel hdvd]
        have hineq : (∑ ψ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (γ k) \
              Work.FeitSibley.scriptSR h.H h.Q1 (γ k ⊔ FSZ h),
              (Work.CharCore.irrDeg ψ) ^ 2)
            ≤ 2 * Work.CharCore.irrDeg (h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁))
              * Work.CharCore.irrDeg χ :=
          hall (h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)) hξS0
            (Work.CharCore.irrDeg χ /
              Work.CharCore.irrDeg (h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁))) hdeg
        -- numerical bookkeeping
        haveI : Fact (Nat.Prime p) := ⟨hp⟩
        have hDpos : (0 : ℝ) < (Nat.card h.D : ℝ) := by
          haveI : Nonempty ↥h.D := ⟨⟨1, h.D.one_mem⟩⟩
          exact_mod_cast Nat.card_pos
        have hQpos : (0 : ℝ) < (Nat.card h.Q1 : ℝ) := by
          haveI : Nonempty ↥h.Q1 := ⟨⟨1, h.Q1.one_mem⟩⟩
          exact_mod_cast Nat.card_pos
        have hZpos : (0 : ℝ) < (Nat.card ↥(FSZ h) : ℝ) := by
          haveI : Nonempty ↥(FSZ h) := ⟨⟨1, (FSZ h).one_mem⟩⟩
          exact_mod_cast Nat.card_pos
        have hZcpos : (0 : ℝ) < (Nat.card ↥(h.centerQ1) : ℝ) := by
          haveI : Nonempty ↥(h.centerQ1) := ⟨⟨1, (h.centerQ1).one_mem⟩⟩
          exact_mod_cast Nat.card_pos
        have hZcge : (Nat.card ↥(FSZ h) : ℝ) ≤ (Nat.card ↥(h.centerQ1) : ℝ) := by
          have hle : FSZ h ≤ h.centerQ1 := by
            intro x hx
            exact h.mem_centerQ1.mpr ⟨hZleQ1 hx, fun y hy =>
              ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2) y hy).symm⟩
          exact_mod_cast card_le_card_of_le hle
        have hZcQ : (Nat.card ↥(h.centerQ1) : ℝ) ≤ (Nat.card h.Q1 : ℝ) := by
          exact_mod_cast card_le_card_of_le h.centerQ1_le_Q1
        have hpq : (Nat.card h.Q1 : ℝ) / (Nat.card ↥(h.centerQ1) : ℝ)
            ≤ (Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ) :=
          div_le_div_of_nonneg_left hQpos.le hZpos hZcge
        have hp_pos : (0 : ℝ) < (Nat.card h.Q1 : ℝ) / (Nat.card ↥(h.centerQ1) : ℝ) := by
          positivity
        have hZge : 2 * (Nat.card h.D : ℝ) + 1 ≤ (Nat.card ↥(FSZ h) : ℝ) := by
          have hoddZ : Odd (Nat.card ↥(FSZ h)) := by
            obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥(FSZ h))).mp (hpg.to_le hZleQ1)
            rw [hn]
            exact (hp.odd_of_ne_two hp2).pow
          have := two_mul_card_D_add_one_le_card_of_odd h (FSZ h) hZleQ1
            (h.D_le_H.trans (FSZ_normal h)) hFSZ hoddZ
          exact_mod_cast this
        have hkne : ((γ k).subgroupOf h.S) ≠ ⊤ := by
          intro htop
          have hle : h.S ≤ γ k := fun x hx => by
            have hx' : (⟨x, hx⟩ : ↥h.S) ∈ (γ k).subgroupOf h.S := by rw [htop]; trivial
            exact Subgroup.mem_subgroupOf.mp hx'
          have hlt : γ k < h.S := lt_of_le_of_lt hγkS' hSlt
          exact (ne_of_lt hlt) (le_antisymm (hγleS k) hle)
        have hI2 : (2 : ℝ) ≤ ((((γ k).subgroupOf h.S).index : ℕ) : ℝ) := by
          haveI : Finite (↥h.S ⧸ (γ k).subgroupOf h.S) := inferInstance
          exact_mod_cast Subgroup.one_lt_index_of_ne_top hkne
        -- the degree bounds
        have hx2 : ((Work.CharCore.irrDeg
              (h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)) : ℝ)) ^ 2
            ≤ (Nat.card h.D : ℝ) ^ 2
              * ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(h.centerQ1) : ℝ)) := by
          have hh := deg_sq_le_of_mem_scriptSR_center h (FSScomm h) h.S (FSScomm_le_S h) le_rfl
            (FSScomm_le_S h) le_rfl hξSR
          have hsub : ((h.S.subgroupOf h.S).index : ℕ) = 1 := by
            rw [Subgroup.subgroupOf_self]; exact Subgroup.index_top
          simpa [hsub] using hh
        have hy2 : ((Work.CharCore.irrDeg χ : ℝ)) ^ 2
            ≤ (Nat.card h.D : ℝ) ^ 2 * ((((γ k).subgroupOf h.S).index : ℕ) : ℝ)
              * ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(h.centerQ1) : ℝ)) :=
          deg_sq_le_of_mem_scriptSR_center h (γ (k+1)) (γ k) (hγleS (k+1)) (hγleS k)
            (hγanti k) (by rw [hγsucc k, Subgroup.commutator_comm]) hχSR
        -- Feit's inequality, in `ℝ`
        have hAx : (∑ ψ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (γ k) \
              Work.FeitSibley.scriptSR h.H h.Q1 (γ k ⊔ FSZ h),
              ((Work.CharCore.irrDeg ψ : ℝ)) ^ 2)
            ≤ 2 * (Work.CharCore.irrDeg
                (h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)) : ℝ)
              * (Work.CharCore.irrDeg χ : ℝ) := by
          exact_mod_cast hineq
        -- the sum formula
        have hsumform := sum_deg_sq_scriptSR_sdiff_gen h (γ k) (FSZ h) (hγleS k) (hγHn k)
          hZleQ1 hZn
        have hZidx : (((FSZ h).subgroupOf h.Q1).index : ℝ)
            = (Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ) := by
          have hcard : Nat.card ↥((FSZ h).subgroupOf h.Q1) = Nat.card ↥(FSZ h) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleQ1).toEquiv
          have hmul := Subgroup.card_mul_index ((FSZ h).subgroupOf h.Q1)
          rw [hcard] at hmul
          have hcast : (Nat.card ↥(FSZ h) : ℝ) * (((FSZ h).subgroupOf h.Q1).index : ℝ)
              = (Nat.card h.Q1 : ℝ) := by exact_mod_cast hmul
          field_simp
          linarith
        have hAineq : (Nat.card h.D : ℝ) * ((((γ k).subgroupOf h.S).index : ℕ) : ℝ)
              * ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ))
              * ((Nat.card ↥(FSZ h) : ℝ) - 1)
            ≤ ∑ ψ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (γ k) \
                Work.FeitSibley.scriptSR h.H h.Q1 (γ k ⊔ FSZ h),
                ((Work.CharCore.irrDeg ψ : ℝ)) ^ 2 := by
          rw [hsumform, hZidx]
          have hZ0 : (Nat.card ↥(FSZ h) : ℝ) ≠ 0 := hZpos.ne'
          have hid : (Nat.card h.Q1 : ℝ) - (Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)
              = ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ))
                * ((Nat.card ↥(FSZ h) : ℝ) - 1) := by
            field_simp
          rw [hid]
          exact le_of_eq (by ring)
        exact numeric_step3 hDpos hI2 hZge hp_pos hpq (by positivity) (by positivity)
          hAx hx2 hy2 hAineq
    have key : ∀ n, 1 ≤ n → n ≤ m → Work.Coherence.Coherent
        (Work.FeitSibley.scriptSR h.H h.Q1 (γ n) \
          Work.FeitSibley.scriptSR h.H h.Q1 (γ n ⊔ FSZ h))
        (Work.FeitSibley.indLin h.H) := by
      intro n
      induction n with
      | zero => intro hn; omega
      | succ j ihj =>
          intro hj1 hjm
          rcases Nat.eq_zero_or_pos j with hj0 | hjpos
          · subst hj0
            simpa using hbase
          · exact step j hjpos (ihj hjpos (by omega))
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h
      · exfalso
        rw [h0, Subgroup.lowerCentralSeries_zero] at hm
        apply hS'bot
        show ⁅h.S, h.S⁆ = ⊥
        rw [hm]
        simp
      · exact h
    have hbot : γ m = ⊥ := hm
    have hfin := key m hm1 le_rfl
    rw [hbot, bot_sup_eq, scriptSR_bot h] at hfin
    exact hfin

end Work.FeitSibley.Coherence
