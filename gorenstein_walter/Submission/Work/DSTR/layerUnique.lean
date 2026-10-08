import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.Dihedral.Defs
import Submission.Work.DSTR.dihedralAbelianRank

namespace Work.DSTR

open DihedralGroup

open scoped commutatorElement

/-! ## Auxiliary facts about dihedral groups -/

/-- In `DihedralGroup n`, a rotation `r i` of order `> 2` (expressed as `2 * i ≠ 0` in `ZMod n`)
has its centralizer inside the rotation subgroup `⟨r⟩`. -/
lemma centralizer_r_le_rot {n : ℕ} (i : ZMod n) (hi : 2 * i ≠ 0) :
    Subgroup.centralizer ({DihedralGroup.r i} : Set (DihedralGroup n)) ≤ Work.Dihedral.rot n := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff] at hy
  have h := hy (DihedralGroup.r i) (by simp)
  rcases Work.Dihedral.eq_r_or_sr y with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact Work.Dihedral.r_mem_rot j
  · exact absurd (two_mul_eq_zero_of_rot_comm_sr j i h) hi

/-- In `DihedralGroup n` (`n ≠ 0`), a noncyclic subgroup `A` all of whose rotations are
involutions (`2 * i = 0`) is contained in its own centralizer, i.e. `C(A) ⊆ A`. -/
lemma centralizer_le_self_of_no_rot {n : ℕ} (hn : n ≠ 0) (A : Subgroup (DihedralGroup n))
    (hnc : ¬ IsCyclic A)
    (hrot : ∀ i : ZMod n, (DihedralGroup.r i : DihedralGroup n) ∈ A → 2 * i = 0) :
    Subgroup.centralizer (A : Set (DihedralGroup n)) ≤ A := by
  -- `A` contains a reflection, since otherwise `A ≤ ⟨r⟩` is cyclic.
  have hx : ∃ u : ZMod n, (DihedralGroup.sr u : DihedralGroup n) ∈ A := by
    by_contra h
    push_neg at h
    have hle : A ≤ Work.Dihedral.rot n := by
      intro x hx
      rcases Work.Dihedral.eq_r_or_sr x with ⟨i, rfl⟩ | ⟨i, hi⟩
      · exact Work.Dihedral.r_mem_rot i
      · exact absurd (hi ▸ hx) (h i)
    exact hnc (Subgroup.isCyclic_of_le (H' := Work.Dihedral.rot n) hle)
  obtain ⟨u, hu⟩ := hx
  -- `A` contains a nontrivial rotation.
  have hρ : ∃ i : ZMod n, (DihedralGroup.r i : DihedralGroup n) ∈ A ∧
      (DihedralGroup.r i : DihedralGroup n) ≠ 1 := by
    by_contra h
    push_neg at h
    have hle : A ≤ Subgroup.zpowers (DihedralGroup.sr u : DihedralGroup n) := by
      intro x hx
      rcases Work.Dihedral.eq_r_or_sr x with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [h i hx]; exact Subgroup.one_mem _
      · have hmem : (DihedralGroup.r (u - i) : DihedralGroup n) ∈ A := by
          rw [← DihedralGroup.sr_mul_sr i u]
          exact mul_mem hx hu
        have hone : (DihedralGroup.sr i * DihedralGroup.sr u : DihedralGroup n) = 1 := by
          rw [DihedralGroup.sr_mul_sr]; exact h (u - i) hmem
        have hinv : (DihedralGroup.sr i : DihedralGroup n) = DihedralGroup.sr u := by
          rw [eq_inv_of_mul_eq_one_right hone, DihedralGroup.inv_sr]
        rw [Subgroup.mem_zpowers_iff]
        exact ⟨1, by rw [zpow_one, DihedralGroup.sr.inj hinv]⟩
    haveI : IsCyclic ↥(Subgroup.zpowers (DihedralGroup.sr u : DihedralGroup n)) :=
      Subgroup.isCyclic_zpowers _
    exact hnc (Subgroup.isCyclic_of_le hle)
  obtain ⟨i, hiA, hine⟩ := hρ
  have h2i : 2 * i = 0 := hrot i hiA
  have hi0 : i ≠ 0 := by
    intro h0
    exact hine (by rw [h0, DihedralGroup.r_zero])
  rcases zmod_two_mul_eq_zero n i h2i with h0 | hhalf
  · exact absurd h0 hi0
  -- the nontrivial rotation of `A` is `r (n / 2)`
  have hρA : (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ∈ A := by
    rw [← hhalf]; exact hiA
  intro y hy
  rw [Subgroup.mem_centralizer_iff] at hy
  rcases Work.Dihedral.eq_r_or_sr y with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · -- `y = r j` commutes with the reflection `sr u`
    have h2j : 2 * j = 0 :=
      two_mul_eq_zero_of_rot_comm_sr u j (hy (DihedralGroup.sr u) hu).symm
    rcases zmod_two_mul_eq_zero n j h2j with h0 | hhalf'
    · rw [h0, DihedralGroup.r_zero]; exact A.one_mem
    · rw [hhalf']; exact hρA
  · -- `y = sr j` commutes with the reflection `sr u`
    have h2j : 2 * (j - u) = 0 :=
      two_mul_sub_eq_zero_of_sr_comm_sr u j (hy (DihedralGroup.sr u) hu).symm
    rcases zmod_two_mul_eq_zero n (j - u) h2j with h0 | hhalf'
    · have : j = u := sub_eq_zero.mp h0
      rw [this]; exact hu
    · have hsr : (DihedralGroup.sr j : DihedralGroup n) =
          DihedralGroup.sr u * DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
        rw [DihedralGroup.sr_mul_r, sub_eq_iff_eq_add.mp hhalf', add_comm]
      rw [hsr]; exact mul_mem hu hρA

/-- If `D ≤ F` are normal subgroups of a group `X` and `F` is quasisimple, then either `D = F`
or `D` commutes elementwise with `F` (i.e. `D ≤ Z(F)`).

The proof passes to the simple quotient `F/Z(F)`: the image of `D` is normal there, so it is
trivial or everything.  In the first case `D ≤ Z(F)`; in the second `F = D·Z(F)`, so `F/D` is a
quotient of the abelian group `Z(F)`, whence `⁅F,F⁆ ≤ D` and, `F` being perfect, `F = D`. -/
lemma normal_le_center_or_eq {X : Type*} [Group X] {D F : Subgroup X} (hD : D.Normal)
    (hF : F.Normal) (hDF : D ≤ F) (hqF : Work.GW2.IsQuasisimple F) :
    D = F ∨ ∀ d ∈ D, ∀ f ∈ F, d * f = f * d := by
  haveI : F.Normal := hF
  set Z : Subgroup ↥F := Subgroup.center ↥F with hZdef
  set π : ↥F →* ↥F ⧸ Z := QuotientGroup.mk' Z with hπdef
  set D' : Subgroup ↥F := D.subgroupOf F with hD'def
  have hD'norm : D'.Normal := by
    rw [hD'def, Subgroup.normal_subgroupOf_iff hDF]
    intro h k hh hk
    exact hD.conj_mem h hh k
  haveI hmap : (D'.map π).Normal := hD'norm.map π (QuotientGroup.mk'_surjective Z)
  rcases hqF.2.eq_bot_or_eq_top_of_normal (D'.map π) with hbot | htop
  · right
    have hle : D' ≤ π.ker := (Subgroup.map_eq_bot_iff D').mp hbot
    intro d hd f hf
    have hmem : (⟨d, hDF hd⟩ : ↥F) ∈ Z := by
      have hker : (⟨d, hDF hd⟩ : ↥F) ∈ (QuotientGroup.mk' Z).ker := by
        rw [MonoidHom.mem_ker]
        exact hle (by simp only [hD'def, Subgroup.mem_subgroupOf]; exact hd)
      rwa [QuotientGroup.ker_mk' Z] at hker
    have hc := (Subgroup.mem_center_iff.mp hmem) (⟨f, hf⟩ : ↥F)
    exact (congrArg Subtype.val hc).symm
  · left
    -- every element of `F` is a product of an element of `D` with a central element
    have hex : ∀ x : ↥F, ∃ d : ↥F, (d : X) ∈ D ∧ ∃ z : ↥F, z ∈ Z ∧ x = d * z := by
      intro x
      have hx : π x ∈ D'.map π := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨d, hd, hdπ⟩ := Subgroup.mem_map.mp hx
      have hdmem : (d : X) ∈ D := by
        rw [hD'def, Subgroup.mem_subgroupOf] at hd
        exact hd
      refine ⟨d, hdmem, d⁻¹ * x, ?_, ?_⟩
      · have hker : d⁻¹ * x ∈ (QuotientGroup.mk' Z).ker := by
          rw [MonoidHom.mem_ker]
          show π (d⁻¹ * x) = 1
          rw [map_mul, map_inv, hdπ, inv_mul_cancel]
        rwa [QuotientGroup.ker_mk' Z] at hker
      · rw [mul_inv_cancel_left]
    have hcomm : ∀ f₁ ∈ F, ∀ f₂ ∈ F, ⁅f₁, f₂⁆ ∈ D := by
      intro f₁ hf₁ f₂ hf₂
      obtain ⟨d₁, hd₁, z₁, hz₁, heq₁⟩ := hex ⟨f₁, hf₁⟩
      obtain ⟨d₂, hd₂, z₂, hz₂, heq₂⟩ := hex ⟨f₂, hf₂⟩
      have hv₁ : f₁ = (d₁ : X) * (z₁ : X) := congrArg Subtype.val heq₁
      have hv₂ : f₂ = (d₂ : X) * (z₂ : X) := congrArg Subtype.val heq₂
      have hd₁F : (d₁ : X) ∈ F := hDF hd₁
      have hd₂F : (d₂ : X) ∈ F := hDF hd₂
      have hz₁F : (z₁ : X) ∈ F := z₁.property
      have hz₂F : (z₂ : X) ∈ F := z₂.property
      have hc₁ : ∀ g : X, g ∈ F → g * (z₁ : X) = (z₁ : X) * g := fun g hg =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hz₁ ⟨g, hg⟩)
      have hc₂ : ∀ g : X, g ∈ F → g * (z₂ : X) = (z₂ : X) * g := fun g hg =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hz₂ ⟨g, hg⟩)
      have key : ⁅(d₁ : X) * (z₁ : X), (d₂ : X) * (z₂ : X)⁆ = ⁅(d₁ : X), (d₂ : X)⁆ := by
        have e1 : ⁅(z₁ : X), (d₂ : X)⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr (hc₁ (d₂ : X) hd₂F).symm
        have e2 : ⁅(z₁ : X), (z₂ : X)⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr (hc₁ (z₂ : X) hz₂F).symm
        have e3 : ⁅(d₁ : X), (z₂ : X)⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr (hc₂ (d₁ : X) hd₁F)
        simp only [commutatorElement_mul_left_eq_conj_mul,
          commutatorElement_mul_right_eq_mul_conj]
        rw [e1, e2, e3]
        group
      rw [hv₁, hv₂, key, commutatorElement_def]
      exact D.mul_mem (D.mul_mem (D.mul_mem hd₁ hd₂) (D.inv_mem hd₁)) (D.inv_mem hd₂)
    have hFD : F ≤ D := hqF.1 ▸ (Subgroup.commutator_le).mpr hcomm
    exact le_antisymm hDF hFD

/-- Distinct normal quasisimple subgroups of a group commute elementwise (distinct components of
a finite group commute). -/
theorem components_commute {X : Type*} [Group X] (E₁ E₂ : Subgroup X)
    (h₁ : E₁.Normal) (h₂ : E₂.Normal) (hq₁ : Work.GW2.IsQuasisimple E₁)
    (hq₂ : Work.GW2.IsQuasisimple E₂) (hne : E₁ ≠ E₂) :
    ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := by
  haveI : E₁.Normal := h₁
  haveI : E₂.Normal := h₂
  intro x hx y hy
  by_cases h12 : E₁ ≤ E₂
  · rcases normal_le_center_or_eq h₁ h₂ h12 hq₂ with heq | hc
    · exact absurd heq hne
    · exact hc x hx y hy
  · by_cases h21 : E₂ ≤ E₁
    · rcases normal_le_center_or_eq h₂ h₁ h21 hq₁ with heq | hc
      · exact absurd heq.symm hne
      · exact (hc y hy x hx).symm
    · -- `E₁ ⊓ E₂` is strictly contained in both, hence centralizes both
      have hD1 : E₁ ⊓ E₂ ≠ E₁ := fun hh => h12 (inf_eq_left.mp hh)
      have hD2 : E₁ ⊓ E₂ ≠ E₂ := fun hh => h21 (inf_eq_right.mp hh)
      have hc1 : ∀ d ∈ E₁ ⊓ E₂, ∀ f ∈ E₁, d * f = f * d := by
        rcases normal_le_center_or_eq (Subgroup.normal_inf_normal E₁ E₂) h₁ inf_le_left hq₁
          with heq | hc
        · exact absurd heq hD1
        · exact hc
      have hc2 : ∀ d ∈ E₁ ⊓ E₂, ∀ f ∈ E₂, d * f = f * d := by
        rcases normal_le_center_or_eq (Subgroup.normal_inf_normal E₁ E₂) h₂ inf_le_right hq₂
          with heq | hc
        · exact absurd heq hD2
        · exact hc
      -- `⁅E₁,E₂⁆ ≤ E₁ ⊓ E₂` centralizes `E₁`
      have hKZ : ⁅E₁, E₂⁆ ≤ Subgroup.centralizer (E₁ : Set X) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (hc1 a ((Subgroup.commutator_le_inf E₁ E₂) ha) b hb).symm
      have hbot : ⁅⁅E₁, E₂⁆, E₁⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hKZ
      have hbot' : ⁅⁅E₂, E₁⁆, E₁⁆ = ⊥ := by
        rw [Subgroup.commutator_comm E₂ E₁]; exact hbot
      -- Hall–Witt (three subgroups lemma)
      have hw := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := E₁) (H₂ := E₁) (H₃ := E₂)
        hbot hbot'
      have hK : ⁅E₁, E₂⁆ = ⊥ := hq₁.1 ▸ hw
      exact commutatorElement_eq_one_iff_mul_comm.mp
        (Subgroup.mem_bot.mp (hK ▸ Subgroup.commutator_mem_commutator hx hy))

/-- **DS5** (`Work.GW2.LayerUniqueProp`): at most one normal quasisimple subgroup.  Two distinct ones commute and have noncyclic Sylow 2-subgroups, producing a commuting 2-subgroup of rank `>= 4` inside a Sylow 2-subgroup of dihedral/cyclic shape. -/
theorem layerUnique (h4 : Work.GW2.QuasisimpleSylowProp)
    (h6 : Work.GW2.QuasisimpleCenterOddProp) (hDR : Work.GW2.DihedralAbelianRankProp) :
    Work.GW2.LayerUniqueProp := by
  intro X _ _ hFT hD E₁ E₂ hN₁ hN₂ hQ₁ hQ₂
  by_contra hne
  -- distinct normal quasisimple subgroups commute
  have hcomm : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x :=
    components_commute E₁ E₂ hN₁ hN₂ hQ₁ hQ₂ hne
  -- Sylow 2-subgroups of `E₁`, `E₂`, viewed inside `X`
  obtain ⟨A⟩ := Sylow.nonempty (p := 2) (G := ↥E₁)
  obtain ⟨B⟩ := Sylow.nonempty (p := 2) (G := ↥E₂)
  have hAnc : ¬ IsCyclic ↥(A : Subgroup ↥E₁) := h4 X hFT E₁ hQ₁ A
  have hBnc : ¬ IsCyclic ↥(B : Subgroup ↥E₂) := h4 X hFT E₂ hQ₂ B
  set A' : Subgroup X := (A : Subgroup ↥E₁).map E₁.subtype with hA'def
  set B' : Subgroup X := (B : Subgroup ↥E₂).map E₂.subtype with hB'def
  have hA'le : A' ≤ E₁ := Subgroup.map_subtype_le _
  have hB'le : B' ≤ E₂ := Subgroup.map_subtype_le _
  have hA'p : IsPGroup 2 ↥A' := (A.isPGroup').map E₁.subtype
  have hB'p : IsPGroup 2 ↥B' := (B.isPGroup').map E₂.subtype
  have hA'nc : ¬ IsCyclic ↥A' := fun hcyc => hAnc
    ((Subgroup.equivMapOfInjective (A : Subgroup ↥E₁) E₁.subtype
      Subtype.coe_injective).isCyclic.mpr hcyc)
  have hB'nc : ¬ IsCyclic ↥B' := fun hcyc => hBnc
    ((Subgroup.equivMapOfInjective (B : Subgroup ↥E₂) E₂.subtype
      Subtype.coe_injective).isCyclic.mpr hcyc)
  have hA'B' : ∀ a ∈ A', ∀ b ∈ B', a * b = b * a := fun a ha b hb =>
    hcomm a (hA'le ha) b (hB'le hb)
  -- `⟨A', B'⟩` is a 2-subgroup of `X`, so it lies in a Sylow 2-subgroup
  have hnorm : A' ≤ Subgroup.normalizer (B' : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    rw [hA'B' a ha b hb, mul_assoc, mul_inv_cancel, mul_one]
    exact hb
  have hSp : IsPGroup 2 ↥(A' ⊔ B') := IsPGroup.to_sup_of_normal_right' hA'p hB'p hnorm
  obtain ⟨P, hSP⟩ := IsPGroup.exists_le_sylow hSp
  have hA'P : A' ≤ (P : Subgroup X) := le_trans le_sup_left hSP
  have hB'P : B' ≤ (P : Subgroup X) := le_trans le_sup_right hSP
  rcases hD P with hPcyc | ⟨n, ⟨e⟩⟩
  · -- the Sylow 2-subgroup of `X` is cyclic: then so is `A'`
    haveI : IsCyclic ↥(P : Subgroup X) := hPcyc
    exact hA'nc (isCyclic_of_injective (Subgroup.inclusion hA'P)
      (Subgroup.inclusion_injective hA'P))
  · -- `P ≅ DihedralGroup n`
    have hn0 : n ≠ 0 := by
      intro hn
      have h1 : Nat.card ↥(P : Subgroup X) = 0 := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hn, mul_zero]
      have h2 : 0 < Nat.card ↥(P : Subgroup X) := Nat.card_pos
      omega
    set A₁ : Subgroup (DihedralGroup n) :=
      (A'.subgroupOf (P : Subgroup X)).map e.toMonoidHom with hA₁def
    set B₁ : Subgroup (DihedralGroup n) :=
      (B'.subgroupOf (P : Subgroup X)).map e.toMonoidHom with hB₁def
    have eA : ↥A' ≃* ↥A₁ :=
      (Subgroup.subgroupOfEquivOfLe hA'P).symm.trans
        (Subgroup.equivMapOfInjective (A'.subgroupOf (P : Subgroup X)) e.toMonoidHom e.injective)
    have eB : ↥B' ≃* ↥B₁ :=
      (Subgroup.subgroupOfEquivOfLe hB'P).symm.trans
        (Subgroup.equivMapOfInjective (B'.subgroupOf (P : Subgroup X)) e.toMonoidHom e.injective)
    have hA₁nc : ¬ IsCyclic ↥A₁ := fun hc => hA'nc (eA.isCyclic.mpr hc)
    have hB₁nc : ¬ IsCyclic ↥B₁ := fun hc => hB'nc (eB.isCyclic.mpr hc)
    have hB₁A₁ : B₁ ≤ Subgroup.centralizer (A₁ : Set (DihedralGroup n)) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      rw [Subgroup.mem_subgroupOf] at hx hy
      have hxy : x * y = y * x := Subtype.ext (hA'B' (x : X) hx (y : X) hy)
      rw [← map_mul, ← map_mul, hxy]
    have hA₁B₁ : A₁ ≤ Subgroup.centralizer (B₁ : Set (DihedralGroup n)) :=
      (Subgroup.le_centralizer_iff).mpr hB₁A₁
    -- if a non-central rotation lies in one of them, the other one is cyclic
    have hcyc_of : ∀ (S T : Subgroup (DihedralGroup n)) (i : ZMod n), 2 * i ≠ 0 →
        S ≤ Subgroup.centralizer (T : Set (DihedralGroup n)) →
        (DihedralGroup.r i : DihedralGroup n) ∈ T → S ≤ Work.Dihedral.rot n := by
      intro S T i hi hST hri
      have hle : Subgroup.centralizer (T : Set (DihedralGroup n)) ≤
          Subgroup.centralizer ({DihedralGroup.r i} : Set (DihedralGroup n)) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff] at hx ⊢
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hx _ hri
      exact hST.trans (hle.trans (centralizer_r_le_rot i hi))
    by_cases hcaseA : ∃ i : ZMod n, (DihedralGroup.r i : DihedralGroup n) ∈ A₁ ∧ 2 * i ≠ 0
    · obtain ⟨i, hi, h2i⟩ := hcaseA
      exact hB₁nc (Subgroup.isCyclic_of_le (hcyc_of B₁ A₁ i h2i hB₁A₁ hi))
    · have hrotA : ∀ i : ZMod n, (DihedralGroup.r i : DihedralGroup n) ∈ A₁ → 2 * i = 0 := by
        intro i hi
        by_contra h2i
        exact hcaseA ⟨i, hi, h2i⟩
      have hAcen : Subgroup.centralizer (A₁ : Set (DihedralGroup n)) ≤ A₁ :=
        centralizer_le_self_of_no_rot hn0 A₁ hA₁nc hrotA
      by_cases hcaseB : ∃ i : ZMod n, (DihedralGroup.r i : DihedralGroup n) ∈ B₁ ∧ 2 * i ≠ 0
      · obtain ⟨i, hi, h2i⟩ := hcaseB
        exact hA₁nc (Subgroup.isCyclic_of_le (hcyc_of A₁ B₁ i h2i hA₁B₁ hi))
      · have hrotB : ∀ i : ZMod n, (DihedralGroup.r i : DihedralGroup n) ∈ B₁ → 2 * i = 0 := by
          intro i hi
          by_contra h2i
          exact hcaseB ⟨i, hi, h2i⟩
        have hBcen : Subgroup.centralizer (B₁ : Set (DihedralGroup n)) ≤ B₁ :=
          centralizer_le_self_of_no_rot hn0 B₁ hB₁nc hrotB
        -- the two Sylow subgroups coincide
        have hAB : A₁ = B₁ := le_antisymm (hA₁B₁.trans hBcen) (hB₁A₁.trans hAcen)
        have hsub : A'.subgroupOf (P : Subgroup X) = B'.subgroupOf (P : Subgroup X) :=
          Subgroup.map_injective e.injective (by rw [← hA₁def, ← hB₁def]; exact hAB)
        have hA'B'eq : A' = B' := by
          have h2 : A' ⊓ (P : Subgroup X) = B' ⊓ (P : Subgroup X) :=
            (Subgroup.subgroupOf_inj).mp hsub
          rwa [inf_eq_left.mpr hA'P, inf_eq_left.mpr hB'P] at h2
        -- `A' ≤ E₁ ⊓ E₂` is central in `E₁`, of even order: contradict `h6`
        have hA'E₂ : A' ≤ E₂ := hA'B'eq ▸ hB'le
        have hcen : A'.subgroupOf E₁ ≤ Subgroup.center ↥E₁ := by
          intro a ha
          rw [Subgroup.mem_subgroupOf] at ha
          rw [Subgroup.mem_center_iff]
          intro g
          exact Subtype.ext (hcomm (g : X) g.property (a : X) (hA'E₂ ha))
        have h2dvd : 2 ∣ Nat.card ↥(Subgroup.center ↥E₁) := by
          have hA'nt : 2 ∣ Nat.card ↥A' := by
            rcases IsPGroup.card_eq_or_dvd hA'p with h1 | hd
            · exact absurd (Nat.card_eq_one_iff_unique.mp h1).1
                (fun hsub => by
                  haveI : Subsingleton ↥A' := hsub
                  exact hA'nc isCyclic_of_subsingleton)
            · exact hd
          have h2dvdA'' : 2 ∣ Nat.card ↥(A'.subgroupOf E₁) := by
            rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'le).toEquiv]
            exact hA'nt
          have hH : Nat.card ↥((A'.subgroupOf E₁).subgroupOf (Subgroup.center ↥E₁)) ∣
              Nat.card ↥(Subgroup.center ↥E₁) := Subgroup.card_subgroup_dvd_card _
          have heq : Nat.card ↥((A'.subgroupOf E₁).subgroupOf (Subgroup.center ↥E₁)) =
              Nat.card ↥(A'.subgroupOf E₁) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcen).toEquiv
          rw [heq] at hH
          exact dvd_trans h2dvdA'' hH
        exact (Nat.not_even_iff_odd.mpr (h6 X hD E₁ hQ₁)) (even_iff_two_dvd.mpr h2dvd)

end Work.DSTR
