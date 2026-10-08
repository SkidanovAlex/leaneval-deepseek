import Mathlib
import Submission.Work.FUS.Defs
import Submission.Work.Dihedral.Defs
import Submission.Work.FUS.DihedralFacts.fourGroup_center_mem
import Submission.Work.FUS.DihedralFacts.exists_conj_reflection_swap
import Submission.Work.FUS.DihedralFacts.centralizer_eq_of_fourGroup
import Submission.Work.FUS.DihedralFacts.isCyclic_or_dihedral_of_le_dihedral
import Submission.Work.FUS.DihedralSylow.subgroup_cyclic_or_dihedral
import Submission.Work.FUS.AutFacts.mulAut_fourGroup_eq_one_of_odd
import Submission.Work.FUS.isPGroup_mulAut_cyclic
import Submission.Work.FUS.isPGroup_mulAut_dihedral
import Submission.Work.FUS.normal_index_two_of_complement
import Submission.OddOrder.Isaacs.Ch05_Transfer.Main

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.FUS

open Subgroup

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

/-! ## Conjugation bookkeeping -/

/-- The pointwise action of a `MulAut` on subgroups is the image under it. -/
lemma smul_eq_map (f : G ≃* G) (H : Subgroup G) : f • H = H.map f.toMonoidHom := by
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  exact Iff.rfl

/-- If `h` normalizes the conjugate-by-`f` of `H`, then `f.symm h` normalizes `H`. -/
lemma symm_mem_normalizer_smul (f : G ≃* G) (H : Subgroup G) {h : G}
    (hh : h ∈ Subgroup.normalizer (f • H : Set G)) :
    f.symm h ∈ Subgroup.normalizer (H : Set G) := by
  have hh' : h ∈ Subgroup.normalizer ((f • H : Subgroup G) : Set G) := hh
  rw [Subgroup.mem_normalizer_iff] at hh' ⊢
  intro v
  constructor
  · intro hv
    have h1 : h * f v * h⁻¹ ∈ f • H := (hh' (f v)).mp ⟨v, hv, rfl⟩
    have h2 : f (f.symm h * v * (f.symm h)⁻¹) ∈ f • H := by
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h1
    rw [Subgroup.mem_smul_pointwise_iff_exists] at h2
    obtain ⟨u, hu, hu'⟩ := h2
    have h3 : u = f.symm h * v * (f.symm h)⁻¹ := f.injective hu'
    rwa [h3] at hu
  · intro hv
    have h1 : f (f.symm h * v * (f.symm h)⁻¹) ∈ f • H := ⟨_, hv, rfl⟩
    have h2 : h * f v * h⁻¹ ∈ f • H := by
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h1
    have h3 : f v ∈ f • H := (hh' (f v)).mpr h2
    rw [Subgroup.mem_smul_pointwise_iff_exists] at h3
    obtain ⟨u, hu, hu'⟩ := h3
    have h4 : u = v := f.injective hu'
    simpa [h4] using hu

/-! ## Sylow conjugacy inside a centralizer -/

/-- If `S` is a Sylow `2`-subgroup whose elements commute with `c`, then any `2`-subgroup `Q`
contained in the centralizer of `c` can be moved into `S` by conjugation by an element of that
centralizer. -/
theorem conj_le_sylow_of_mem_centralizer (S : Sylow 2 G) (c : G)
    (hc : ∀ x ∈ (S : Subgroup G), x * c = c * x)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hQc : Q ≤ Subgroup.centralizer ({c} : Set G)) :
    ∃ x : G, x ∈ Subgroup.centralizer ({c} : Set G) ∧
      ∀ y ∈ Q, x * y * x⁻¹ ∈ (S : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer ({c} : Set G) with hC
  have hSleC : (S : Subgroup G) ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (hc x hx).symm
  haveI : Finite ↥C := Subtype.finite
  let S' : Sylow 2 ↥C := S.subtype hSleC
  have hQ' : IsPGroup 2 (Q.subgroupOf C) :=
    IsPGroup.comap_of_injective hQ C.subtype Subtype.coe_injective
  obtain ⟨T, hQT⟩ := hQ'.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (M := ↥C) T S'
  have hy' : (MulAut.conj (y : ↥C)) • (T : Subgroup ↥C) = (S' : Subgroup ↥C) :=
    congrArg (fun P : Sylow 2 ↥C => (P : Subgroup ↥C)) hy
  refine ⟨(y : G), y.2, ?_⟩
  intro z hz
  have hzT : (⟨z, hQc hz⟩ : ↥C) ∈ (T : Subgroup ↥C) :=
    hQT (Subgroup.mem_subgroupOf.mpr hz)
  have hmem : (MulAut.conj (y : ↥C)) (⟨z, hQc hz⟩ : ↥C) ∈ (S' : Subgroup ↥C) := by
    rw [← hy', Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨_, hzT, rfl⟩
  have hcoe : ((MulAut.conj (y : ↥C)) (⟨z, hQc hz⟩ : ↥C) : G) = (y : G) * z * (y : G)⁻¹ := by
    rw [MulAut.conj_apply]
    rfl
  have hmem' : (y : G) * z * (y : G)⁻¹ ∈ (S : Subgroup G) := by
    rw [← hcoe]
    exact Subgroup.mem_subgroupOf.mp hmem
  exact hmem'

/-! ## Elementary structure of a four-group -/

/-- A subgroup of order `4` in which every element is an involution is abelian. -/
lemma fourGroup_comm (V : Subgroup G) (hV : Work.GW2.IsFourGroup V) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a := by
  have ha2 : a * a = 1 := by simpa [pow_two] using hV.2 a ha
  have hb2 : b * b = 1 := by simpa [pow_two] using hV.2 b hb
  have hab2 : (a * b) * (a * b) = 1 := by
    simpa [pow_two] using hV.2 (a * b) (V.mul_mem ha hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab2).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right hb2, inv_eq_of_mul_eq_one_right ha2]

/-- A non-identity element of a four-group has order two. -/
lemma fourGroup_orderOf (V : Subgroup G) (hV : Work.GW2.IsFourGroup V) {v : G} (hv : v ∈ V)
    (hv1 : v ≠ 1) : orderOf v = 2 := by
  have hdvd : orderOf v ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hV.2 v hv)
  have hne : orderOf v ≠ 1 := fun h => hv1 (orderOf_eq_one_iff.mp h)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd h hne
  · exact h

/-- Given two distinct non-identity elements `x`, `y` of a four-group `V`, every non-identity
element of `V` is `x`, `y` or a third element `z`. -/
lemma fourGroup_third (V : Subgroup G) (hV : Work.GW2.IsFourGroup V) {x y : G} (hx : x ∈ V)
    (hx1 : x ≠ 1) (hy : y ∈ V) (hy1 : y ≠ 1) (hxy : x ≠ y) :
    ∃ z ∈ V, z ≠ 1 ∧ z ≠ x ∧ z ≠ y ∧ ∀ w ∈ V, w ≠ 1 → w = x ∨ w = y ∨ w = z := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have hcard : Fintype.card V = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact hV.1
  set xv : V := ⟨x, hx⟩ with hxv
  set yv : V := ⟨y, hy⟩ with hyv
  have hxne : xv ≠ 1 := fun h => hx1 (Subtype.ext_iff.mp h)
  have hyne : yv ≠ 1 := fun h => hy1 (Subtype.ext_iff.mp h)
  have hxyne : xv ≠ yv := fun h => hxy (Subtype.ext_iff.mp h)
  have hcard3 : ({1, xv, yv} : Finset V).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨1, xv, yv, Ne.symm hxne, Ne.symm hyne, hxyne, rfl⟩
  obtain ⟨zv, hzvnot⟩ : ∃ zv : V, zv ∉ ({1, xv, yv} : Finset V) := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset V) ⊆ ({1, xv, yv} : Finset V) := fun u _ => h u
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard, hcard3] at hle
    omega
  have hzv1 : zv ≠ 1 := fun h => hzvnot (by simp [h])
  have hzvx : zv ≠ xv := fun h => hzvnot (by simp [h])
  have hzvy : zv ≠ yv := fun h => hzvnot (by simp [h])
  refine ⟨(zv : G), zv.2, ?_, ?_, ?_, ?_⟩
  · intro h; exact hzv1 (Subtype.ext h)
  · intro h; exact hzvx (Subtype.ext h)
  · intro h; exact hzvy (Subtype.ext h)
  · intro w hw hw1
    have hset : ({1, xv, yv, zv} : Finset V) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcard, Finset.card_eq_four]
      exact ⟨1, xv, yv, zv, Ne.symm hxne, Ne.symm hyne, Ne.symm hzv1, hxyne,
        Ne.symm hzvx, Ne.symm hzvy, rfl⟩
    have hwmem : (⟨w, hw⟩ : V) ∈ ({1, xv, yv, zv} : Finset V) := by
      rw [hset]; exact Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwmem
    rcases hwmem with h | h | h | h
    · exact absurd (Subtype.ext_iff.mp h) hw1
    · exact Or.inl (by rw [hxv] at h; exact Subtype.ext_iff.mp h)
    · exact Or.inr (Or.inl (by rw [hyv] at h; exact Subtype.ext_iff.mp h))
    · exact Or.inr (Or.inr (Subtype.ext_iff.mp h))

/-- A four-group with two named distinct non-identity elements `a`, `b` consists exactly of
`1`, `a`, `b` and `a * b`. -/
lemma fourGroup_mem_cases (V : Subgroup G) (hV : Work.GW2.IsFourGroup V) {a b : G}
    (ha : a ∈ V) (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    ∀ y ∈ V, y = 1 ∨ y = a ∨ y = b ∨ y = a * b := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have hcard : Fintype.card V = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact hV.1
  have haa : a * a = 1 := by simpa [pow_two] using hV.2 a ha
  have hbb : b * b = 1 := by simpa [pow_two] using hV.2 b hb
  have habV : a * b ∈ V := V.mul_mem ha hb
  have h1 : a * b ≠ 1 := by
    intro h
    exact hab (mul_left_cancel (by rw [h, haa]))
  have h2 : a * b ≠ a := by
    intro h
    exact hb1 (mul_left_cancel (by rw [h, mul_one]))
  have h3 : a * b ≠ b := by
    intro h
    exact ha1 (mul_right_cancel (by rw [one_mul, h]))
  have hS : ({1, a, b, a * b} : Finset G).card = 4 := by
    rw [Finset.card_eq_four]
    exact ⟨1, a, b, a * b, ha1.symm, hb1.symm, h1.symm, hab, h2.symm, h3.symm, rfl⟩
  have hsub : ({1, a, b, a * b} : Finset G) ⊆ (Finset.univ : Finset V).image Subtype.val := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz | hz
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, hz.symm⟩
    · exact Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, hz.symm⟩
    · exact Finset.mem_image.mpr ⟨⟨b, hb⟩, Finset.mem_univ _, hz.symm⟩
    · exact Finset.mem_image.mpr ⟨⟨a * b, habV⟩, Finset.mem_univ _, hz.symm⟩
  have hcard' : ((Finset.univ : Finset V).image Subtype.val).card = 4 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ, hcard]
  have heq : ({1, a, b, a * b} : Finset G) = (Finset.univ : Finset V).image Subtype.val :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard', hS])
  intro y hy
  have hy' : y ∈ ({1, a, b, a * b} : Finset G) := by
    rw [heq]
    exact Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_univ _, rfl⟩
  simpa using hy'

/-! ## The transitivity criterion -/

/-- If the conjugation action of `N_G(V)` on `V#` has no fixed point then it is transitive on
`V#`: with only three non-identity elements a non-transitive action has a fixed point. -/
lemma exists_conj_mem_normalizer_of_no_fixed
    (V : Subgroup G) (hV : Work.GW2.IsFourGroup V)
    (hfix : ∀ w ∈ V, w ≠ 1 →
      ¬ (Subgroup.normalizer (V : Set G) ≤ Subgroup.centralizer ({w} : Set G)))
    (x : G) (hx : x ∈ V) (hx1 : x ≠ 1) (y : G) (hy : y ∈ V) (hy1 : y ≠ 1) :
    ∃ g ∈ Subgroup.normalizer (V : Set G), g * x * g⁻¹ = y := by
  classical
  set N : Subgroup G := Subgroup.normalizer (V : Set G) with hN
  by_cases hxy : x = y
  · exact ⟨1, N.one_mem, by rw [hxy]; simp⟩
  by_contra hcon
  push_neg at hcon
  have hcon' : ¬ ∃ g ∈ N, g * x * g⁻¹ = y := by
    rintro ⟨g, hg, hg'⟩; exact hcon g hg hg'
  have hNm : ∀ g ∈ N, ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    intro g hg v hv
    exact (Subgroup.mem_normalizer_iff.mp hg v).mp hv
  have hne : ∀ g ∈ N, ∀ v ∈ V, v ≠ 1 → g * v * g⁻¹ ≠ 1 := by
    intro g hg v hv hv1 h
    have hv' : v = 1 := by
      have hv'' : v = g⁻¹ * (g * v * g⁻¹) * g := by group
      rw [hv'', h]; simp
    exact hv1 hv'
  have hsymm : ∀ {u v : G}, (∃ g ∈ N, g * u * g⁻¹ = v) → (∃ g ∈ N, g * v * g⁻¹ = u) := by
    rintro u v ⟨g, hg, hg'⟩
    refine ⟨g⁻¹, N.inv_mem hg, ?_⟩
    rw [← hg']
    group
  have htrans : ∀ {u v w : G}, (∃ g ∈ N, g * u * g⁻¹ = v) →
      (∃ g ∈ N, g * v * g⁻¹ = w) → (∃ g ∈ N, g * u * g⁻¹ = w) := by
    rintro u v w ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
    refine ⟨g₂ * g₁, N.mul_mem hg₂ hg₁, ?_⟩
    calc g₂ * g₁ * u * (g₂ * g₁)⁻¹ = g₂ * (g₁ * u * g₁⁻¹) * g₂⁻¹ := by group
      _ = g₂ * v * g₂⁻¹ := by rw [h₁]
      _ = w := h₂
  obtain ⟨z, hzV, hz1, hzx, hzy, hcover⟩ := fourGroup_third V hV hx hx1 hy hy1 hxy
  by_cases hz_conj : ∃ g ∈ N, g * z * g⁻¹ = x
  · have hyfix : ∀ g ∈ N, g * y * g⁻¹ = y := by
      intro g hg
      have hmemV : g * y * g⁻¹ ∈ V := hNm g hg y hy
      have hne1 : g * y * g⁻¹ ≠ 1 := hne g hg y hy hy1
      rcases hcover (g * y * g⁻¹) hmemV hne1 with h | h | h
      · exact absurd (hsymm ⟨g, hg, h⟩) hcon'
      · exact h
      · rcases hz_conj with ⟨g₀, hg₀, hg₀'⟩
        refine absurd ?_ hcon'
        refine hsymm ⟨g₀ * g, N.mul_mem hg₀ hg, ?_⟩
        rw [show g₀ * g * y * (g₀ * g)⁻¹ = g₀ * (g * y * g⁻¹) * g₀⁻¹ by group, h, hg₀']
    refine absurd ?_ (hfix y hy hy1)
    rintro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (mul_inv_eq_iff_eq_mul.mp (hyfix g hg)).symm
  · push_neg at hz_conj
    have hxfix : ∀ g ∈ N, g * x * g⁻¹ = x := by
      intro g hg
      have hmemV : g * x * g⁻¹ ∈ V := hNm g hg x hx
      have hne1 : g * x * g⁻¹ ≠ 1 := hne g hg x hx hx1
      rcases hcover (g * x * g⁻¹) hmemV hne1 with h | h | h
      · exact h
      · exact absurd ⟨g, hg, h⟩ hcon'
      · exact absurd (hsymm ⟨g, hg, h⟩) (by
          rintro ⟨g', hg', hg''⟩; exact hz_conj g' hg' hg'')
    refine absurd ?_ (hfix x hx hx1)
    rintro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (mul_inv_eq_iff_eq_mul.mp (hxfix g hg)).symm

/-! ## Classification of the four-groups of a dihedral group -/

section DihedralClasses

open DihedralGroup

/-- In `ZMod n` with `n` even, `2 * m ≠ 1`. -/
lemma zmod_two_mul_ne_one (n : ℕ) [NeZero n] (h2 : 2 ∣ n) (m : ZMod n) :
    (2 : ZMod n) * m ≠ 1 := by
  intro h
  have h' := congrArg (ZMod.castHom h2 (ZMod 2)) h
  rw [map_mul, map_one] at h'
  have h2c : (ZMod.castHom h2 (ZMod 2)) (2 : ZMod n) = 0 := by
    have h2n : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
    have : (ZMod.castHom h2 (ZMod 2)) ((2 : ℕ) : ZMod n) = 0 := by
      rw [map_natCast]; exact h2n
    simpa using this
  rw [h2c, zero_mul] at h'
  exact zero_ne_one h'

/-- The central rotation `r (n/2)` of `DihedralGroup n` (`n` even) is central. -/
lemma dihedral_r_half_central (n : ℕ) [NeZero n] (heven : Even n) (y : DihedralGroup n) :
    y * DihedralGroup.r ((n / 2 : ℕ) : ZMod n)
      = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * y := by
  have hhalf : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
    obtain ⟨r, hr⟩ := heven
    rw [← Nat.cast_add, show n / 2 + n / 2 = n by omega, ZMod.natCast_self]
  rcases Work.Dihedral.eq_r_or_sr y with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
  · rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
    congr 1
    rw [sub_eq_add_neg]
    have hneg : -(((n / 2 : ℕ)) : ZMod n) = ((n / 2 : ℕ) : ZMod n) :=
      (neg_eq_iff_add_eq_zero).mpr hhalf
    rw [hneg]

/-- A multiple of `4` is even. -/
lemma even_of_four_dvd {m : ℕ} (h : 4 ∣ m) : Even m := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨2 * k, by ring⟩

/-- Every conjugate of the reflection `sr 0` is of the form `sr (2 * m)`. -/
lemma conj_sr_zero_eq (n : ℕ) (d : DihedralGroup n) :
    ∃ m : ZMod n, d * DihedralGroup.sr (0 : ZMod n) * d⁻¹ = DihedralGroup.sr (2 * m) := by
  rcases Work.Dihedral.eq_r_or_sr d with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact ⟨-t, by rw [Work.Dihedral.r_conj_sr]; congr 1; ring⟩
  · exact ⟨t, by rw [Work.Dihedral.sr_conj_sr]; congr 1; ring⟩

/-- Every reflection of `DihedralGroup n` (`4 ∣ n`) is conjugate to `sr 0` or `sr 1`. -/
lemma reflection_conj_sr_zero_or_one (n : ℕ) [NeZero n] (h4 : 4 ∣ n) (i : ZMod n) :
    (∃ d : DihedralGroup n, d * DihedralGroup.sr i * d⁻¹ = DihedralGroup.sr 0) ∨
      (∃ d : DihedralGroup n, d * DihedralGroup.sr i * d⁻¹ = DihedralGroup.sr 1) := by
  have key : ∃ t : ZMod n, i - 2 * t = 0 ∨ i - 2 * t = 1 := by
    refine ⟨((i.val / 2 : ℕ) : ZMod n), ?_⟩
    have hnat : 2 * (i.val / 2) = i.val - i.val % 2 := by omega
    have h2t : 2 * ((i.val / 2 : ℕ) : ZMod n) = i - ((i.val % 2 : ℕ) : ZMod n) := by
      calc 2 * ((i.val / 2 : ℕ) : ZMod n)
          = ((2 * (i.val / 2) : ℕ) : ZMod n) := by push_cast; ring
        _ = ((i.val - i.val % 2 : ℕ) : ZMod n) := by rw [hnat]
        _ = (i.val : ZMod n) - ((i.val % 2 : ℕ) : ZMod n) := by
              rw [Nat.cast_sub (Nat.mod_le i.val 2)]
        _ = i - ((i.val % 2 : ℕ) : ZMod n) := by rw [ZMod.natCast_zmod_val]
    rw [h2t]
    rcases (by omega : i.val % 2 = 0 ∨ i.val % 2 = 1) with h | h
    · rw [h]
      left
      push_cast
      abel
    · rw [h]
      right
      push_cast
      abel
  obtain ⟨t, ht⟩ := key
  rcases ht with h | h
  · exact Or.inl ⟨DihedralGroup.r t, by rw [Work.Dihedral.r_conj_sr, h]⟩
  · exact Or.inr ⟨DihedralGroup.r t, by rw [Work.Dihedral.r_conj_sr, h]⟩

/-- The four-group `{1, r (n/2), sr e, r (n/2) * sr e}` of `DihedralGroup n` (`n` even). -/
def fourEl (n : ℕ) (heven : Even n) (e : ZMod n) : Subgroup (DihedralGroup n) where
  carrier := {x | x = 1 ∨ x = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) ∨ x = DihedralGroup.sr e ∨
    x = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * DihedralGroup.sr e}
  mul_mem' := by
    have hhalf : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
      obtain ⟨r, hr⟩ := heven
      rw [← Nat.cast_add, show n / 2 + n / 2 = n by omega, ZMod.natCast_self]
    have hc2 : DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * DihedralGroup.r ((n / 2 : ℕ) : ZMod n)
        = 1 := by
      rw [DihedralGroup.r_mul_r, hhalf, DihedralGroup.r_zero]
    have hy2 : DihedralGroup.sr e * DihedralGroup.sr e = 1 := by
      rw [DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]
    have hcy : DihedralGroup.sr e * DihedralGroup.r ((n / 2 : ℕ) : ZMod n)
        = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * DihedralGroup.sr e := by
      rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
      congr 1
      rw [sub_eq_add_neg]
      have hneg : -(((n / 2 : ℕ)) : ZMod n) = ((n / 2 : ℕ) : ZMod n) :=
        (neg_eq_iff_add_eq_zero).mpr hhalf
      rw [hneg]
    intro a b ha hb
    rcases ha with h | h | h | h <;> rcases hb with h2 | h2 | h2 | h2 <;> rw [h, h2]
    · exact Or.inl (one_mul 1)
    · exact Or.inr (Or.inl (one_mul _))
    · exact Or.inr (Or.inr (Or.inl (one_mul _)))
    · exact Or.inr (Or.inr (Or.inr (one_mul _)))
    · exact Or.inr (Or.inl (mul_one _))
    · exact Or.inl hc2
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, hc2, one_mul])))
    · exact Or.inr (Or.inr (Or.inl (mul_one _)))
    · exact Or.inr (Or.inr (Or.inr hcy))
    · exact Or.inl hy2
    · exact Or.inr (Or.inl (by rw [← mul_assoc, hcy, mul_assoc, hy2, mul_one]))
    · exact Or.inr (Or.inr (Or.inr (mul_one _)))
    · exact Or.inr (Or.inr (Or.inl (by rw [mul_assoc, hcy, ← mul_assoc, hc2, one_mul])))
    · exact Or.inr (Or.inl (by rw [mul_assoc, hy2, mul_one]))
    · exact Or.inl (by
        rw [show (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * DihedralGroup.sr e)
            * (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * DihedralGroup.sr e)
            = DihedralGroup.r ((n / 2 : ℕ) : ZMod n)
              * (DihedralGroup.sr e * DihedralGroup.r ((n / 2 : ℕ) : ZMod n))
              * DihedralGroup.sr e from by group,
          hcy, ← mul_assoc, hc2, one_mul, hy2])
  one_mem' := Or.inl rfl
  inv_mem' := by
    have hhalf : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
      obtain ⟨r, hr⟩ := heven
      rw [← Nat.cast_add, show n / 2 + n / 2 = n by omega, ZMod.natCast_self]
    have hc2 : DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * DihedralGroup.r ((n / 2 : ℕ) : ZMod n)
        = 1 := by
      rw [DihedralGroup.r_mul_r, hhalf, DihedralGroup.r_zero]
    have hy2 : DihedralGroup.sr e * DihedralGroup.sr e = 1 := by
      rw [DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]
    have hcy : DihedralGroup.sr e * DihedralGroup.r ((n / 2 : ℕ) : ZMod n)
        = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * DihedralGroup.sr e := by
      rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
      congr 1
      rw [sub_eq_add_neg]
      have hneg : -(((n / 2 : ℕ)) : ZMod n) = ((n / 2 : ℕ) : ZMod n) :=
        (neg_eq_iff_add_eq_zero).mpr hhalf
      rw [hneg]
    intro a ha
    rcases ha with h | h | h | h <;> rw [h]
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hc2))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hy2)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hy2, inv_eq_of_mul_eq_one_right hc2, hcy]

lemma mem_fourEl (n : ℕ) (heven : Even n) (e : ZMod n) {x : DihedralGroup n} :
    x ∈ fourEl n heven e ↔ x = 1 ∨ x = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) ∨
      x = DihedralGroup.sr e ∨
        x = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * DihedralGroup.sr e :=
  Iff.rfl

lemma fourEl_eq_closure (n : ℕ) (heven : Even n) (e : ZMod n) :
    fourEl n heven e = Subgroup.closure ({DihedralGroup.r ((n / 2 : ℕ) : ZMod n),
      DihedralGroup.sr e} : Set (DihedralGroup n)) := by
  apply le_antisymm
  · intro x hx
    rw [mem_fourEl] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Or.inl rfl)
    · exact Subgroup.subset_closure (Or.inr rfl)
    · exact Subgroup.mul_mem _
        (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact (mem_fourEl n heven e).mpr (Or.inr (Or.inl rfl))
    · exact (mem_fourEl n heven e).mpr (Or.inr (Or.inr (Or.inl rfl)))
end DihedralClasses

/-! ## The case `|S| = 4` -/

/-- If the Sylow 2-subgroup has order `4`, no four-group `V ≤ S` has its normalizer contained in
the centralizer of a non-identity element of `V`. -/
lemma bad_false_of_card_four (S : Sylow 2 G) (hcard : Nat.card (S : Subgroup G) = 4)
    (hconj : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (W : Subgroup G) (hW : Work.GW2.IsFourGroup W) (hWS : W ≤ (S : Subgroup G))
    (w : G) (hw : w ∈ W) (hw1 : w ≠ 1)
    (hbad : Subgroup.normalizer (W : Set G) ≤ Subgroup.centralizer ({w} : Set G)) : False := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype W := Fintype.ofFinite W
  have hWeq : W = (S : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hWS (by rw [hcard, hW.1])
  obtain ⟨v, hv, hv1, hvw⟩ : ∃ v ∈ W, v ≠ 1 ∧ v ≠ w := by
    by_contra h
    push_neg at h
    have hone : ∀ u ∈ W, u = 1 ∨ u = w := by
      intro u hu
      by_cases h1 : u = 1
      · exact Or.inl h1
      · exact Or.inr (h u hu h1)
    have hsub : (Finset.univ : Finset W).image Subtype.val ⊆ ({1, w} : Finset G) := by
      intro u hu
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hu
      rcases hone a a.2 with h' | h' <;> simp [h']
    have h1 : ((Finset.univ : Finset W).image Subtype.val).card = 4 := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ,
        ← Nat.card_eq_fintype_card, hW.1]
    have h2 : ({1, w} : Finset G).card = 2 := by
      rw [Finset.card_eq_two]; exact ⟨1, w, hw1.symm, rfl⟩
    have := Finset.card_le_card hsub
    omega
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj v w (fourGroup_orderOf W hW hv hv1)
    (fourGroup_orderOf W hW hw hw1))
  haveI : IsMulCommutative (S : Subgroup G) := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have ha : (a : G) ∈ W := by rw [hWeq]; exact a.2
    have hb : (b : G) ∈ W := by rw [hWeq]; exact b.2
    exact fourGroup_comm W hW ha hb
  have hvS : v ∈ (S : Subgroup G) := by rw [← hWeq]; exact hv
  have hygS : (c⁻¹)⁻¹ * v * c⁻¹ ∈ (S : Subgroup G) := by
    rw [inv_inv, hc, ← hWeq]
    exact hw
  obtain ⟨nn, hnn, hfus⟩ := S.conj_eq_normalizer_conj_of_mem v (c⁻¹) hvS hygS
  have hw' : w = nn⁻¹ * v * nn := by
    rw [inv_inv] at hfus
    rw [← hc]
    exact hfus
  have hnnW : nn ∈ Subgroup.normalizer (W : Set G) := by
    rw [hWeq]; exact hnn
  have hfixw : nn * w * nn⁻¹ = w := by
    have hcent := hbad hnnW
    rw [Subgroup.mem_centralizer_iff] at hcent
    have hcomm : w * nn = nn * w := hcent w (Set.mem_singleton w)
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hv_eq : v = w := by
    have h2 : nn * w * nn⁻¹ = v := by rw [hw']; group
    rw [← h2, hfixw]
  exact hvw hv_eq

/-! ## The four-groups of a Sylow subgroup, transported -/

/-- The four-group `{1, c, y_i, c * y_i}` of `G`, where `y_i` is the element of the Sylow
2-subgroup `S` corresponding to the reflection `sr i` of `DihedralGroup n`. -/
noncomputable def fourOf (S : Sylow 2 G) (n : ℕ) (h4 : 4 ∣ n)
    (e : (S : Subgroup G) ≃* DihedralGroup n) (i : ZMod n) : Subgroup G :=
  ((fourEl n (even_of_four_dvd h4) i).comap e.toMonoidHom).map (S : Subgroup G).subtype

lemma fourOf_le (S : Sylow 2 G) (n : ℕ) (h4 : 4 ∣ n)
    (e : (S : Subgroup G) ≃* DihedralGroup n) (i : ZMod n) :
    fourOf S n h4 e i ≤ (S : Subgroup G) := Subgroup.map_subtype_le _

lemma mem_fourOf (S : Sylow 2 G) (n : ℕ) (h4 : 4 ∣ n)
    (e : (S : Subgroup G) ≃* DihedralGroup n) (i : ZMod n) {x : G}
    (hx : x ∈ (S : Subgroup G)) :
    x ∈ fourOf S n h4 e i ↔ e ⟨x, hx⟩ ∈ fourEl n (even_of_four_dvd h4) i := by
  constructor
  · intro h
    rw [fourOf, Subgroup.mem_map] at h
    obtain ⟨s, hs, hxs⟩ := h
    have h2 : s = ⟨x, hx⟩ := Subtype.ext hxs
    rwa [h2] at hs
  · intro h
    rw [fourOf, Subgroup.mem_map]
    exact ⟨⟨x, hx⟩, h, rfl⟩

/-- The central involution of a Sylow `2`-subgroup (`S ≅ D_n`, `4 ≤ n`) lies in every four-group
of `S`. -/
lemma fourOf_center_mem (S : Sylow 2 G) (n : ℕ) (hn : 4 ≤ n) (h4 : 4 ∣ n)
    (e : (S : Subgroup G) ≃* DihedralGroup n) (Z : Subgroup G)
    (hZ : Work.GW2.IsFourGroup Z) (hZS : Z ≤ (S : Subgroup G)) :
    ((e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) : (S : Subgroup G)) : G) ∈ Z := by
  haveI : NeZero n := ⟨by omega⟩
  have hWmap : Work.GW2.IsFourGroup ((Z.subgroupOf (S : Subgroup G)).map e.toMonoidHom) := by
    refine ⟨?_, ?_⟩
    · rw [Subgroup.card_map_of_injective e.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv]
      exact hZ.1
    · intro v hv
      rw [Subgroup.mem_map] at hv
      obtain ⟨y, hy, rfl⟩ := hv
      have hyy : y * y = 1 := Subtype.ext (by
        show (y : G) * (y : G) = (1 : G)
        rw [← pow_two]
        exact hZ.2 (y : G) (Subgroup.mem_subgroupOf.mp hy))
      rw [← map_pow, show y ^ 2 = 1 from by rw [pow_two]; exact hyy, map_one]
  have hmem := DihedralFacts.fourGroup_center_mem n hn _ hWmap
  rw [Subgroup.mem_map] at hmem
  obtain ⟨y, hy, hyy⟩ := hmem
  have hy' : y = e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) := by
    apply e.injective
    show e.toMonoidHom y = e.toMonoidHom (e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)))
    rw [hyy]
    exact (MulEquiv.apply_symm_apply e (DihedralGroup.r ((n / 2 : ℕ) : ZMod n))).symm
  simpa [hy'] using Subgroup.mem_subgroupOf.mp hy

/-- Rewriting a conjugate through the isomorphism `e`. -/
lemma map_conj_elem (S : Sylow 2 G) (n : ℕ) (e : (S : Subgroup G) ≃* DihedralGroup n)
    {d z : G} (hd : d ∈ (S : Subgroup G)) (hz : z ∈ (S : Subgroup G))
    (hy : d * z * d⁻¹ ∈ (S : Subgroup G)) :
    e ⟨d * z * d⁻¹, hy⟩ = e ⟨d, hd⟩ * e ⟨z, hz⟩ * (e ⟨d, hd⟩)⁻¹ := by
  rw [show (⟨d * z * d⁻¹, hy⟩ : (S : Subgroup G)) =
      ⟨d, hd⟩ * ⟨z, hz⟩ * (⟨d, hd⟩)⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]

/-- Every four-group of `S` is `S`-conjugate to `fourOf 0` or `fourOf 1`. -/
lemma fourGroup_conj_fourOf (S : Sylow 2 G) (n : ℕ) (hn : 4 ≤ n) (h4 : 4 ∣ n)
    (e : (S : Subgroup G) ≃* DihedralGroup n) (Z : Subgroup G)
    (hZ : Work.GW2.IsFourGroup Z) (hZS : Z ≤ (S : Subgroup G)) :
    (∃ d ∈ (S : Subgroup G), (MulAut.conj d) • Z = fourOf S n h4 e 0) ∨
      (∃ d ∈ (S : Subgroup G), (MulAut.conj d) • Z = fourOf S n h4 e 1) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have heven : Even n := even_of_four_dvd h4
  set c : G := ((e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) : (S : Subgroup G)) : G) with hcdef
  have hcS : c ∈ (S : Subgroup G) := (e.symm _).2
  have hce : e ⟨c, hcS⟩ = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
    rw [show (⟨c, hcS⟩ : (S : Subgroup G)) = e.symm (DihedralGroup.r _) from Subtype.ext rfl]
    exact MulEquiv.apply_symm_apply e _
  have hcZ : c ∈ Z := fourOf_center_mem S n hn h4 e Z hZ hZS
  have hc1 : c ≠ 1 := by
    intro h
    have h0 : DihedralGroup.r ((n / 2 : ℕ) : ZMod n) = 1 := by
      have h1 : (⟨c, hcS⟩ : (S : Subgroup G)) = 1 := Subtype.ext h
      rw [← hce, h1, map_one]
    have h00 : ((n / 2 : ℕ) : ZMod n) = 0 := DihedralGroup.r.inj h0
    have hval : ((n / 2 : ℕ) : ZMod n).val = 0 := by rw [h00, ZMod.val_zero]
    rw [ZMod.val_natCast_of_lt (by omega : n / 2 < n)] at hval
    omega
  -- find a "reflection" in `Z`
  obtain ⟨x, hxZ, hx1, hxnotR⟩ : ∃ x : G, ∃ hxZ : x ∈ Z, x ≠ 1 ∧
      e ⟨x, hZS hxZ⟩ ∉ Work.Dihedral.rot n := by
    by_contra h
    push_neg at h
    haveI : Fintype Z := Fintype.ofFinite Z
    have hcard : Fintype.card Z = 4 := by rw [← Nat.card_eq_fintype_card]; exact hZ.1
    have hsub : (Finset.univ : Finset Z).image Subtype.val ⊆ ({1, c} : Finset G) := by
      intro z hz
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
      by_cases h1 : (a : G) = 1
      · simp [h1]
      · have h2 := h (a : G) a.2 h1
        have h3 : e ⟨(a : G), hZS a.2⟩ = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
          have hsq : (e ⟨(a : G), hZS a.2⟩) ^ 2 = 1 := by
            have hyy : (⟨(a : G), hZS a.2⟩ : (S : Subgroup G)) ^ 2 = 1 := Subtype.ext (by
              show (a : G) ^ 2 = (1 : G)
              exact hZ.2 (a : G) a.2)
            rw [← map_pow, hyy, map_one]
          rcases DihedralFacts.rot_involution_eq n heven h2 hsq with h4 | h4
          · refine absurd ?_ h1
            have h5 : (⟨(a : G), hZS a.2⟩ : (S : Subgroup G)) = 1 :=
              e.injective (by rw [h4]; exact (map_one e).symm)
            exact Subtype.ext_iff.mp h5
          · exact h4
        have h4 : (⟨(a : G), hZS a.2⟩ : (S : Subgroup G)) = ⟨c, hcS⟩ :=
          e.injective (by rw [h3, hce])
        have h5 : (a : G) = c := Subtype.ext_iff.mp h4
        simp [h5]
    have h1 : ((Finset.univ : Finset Z).image Subtype.val).card = 4 := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ, hcard]
    have h2 : ({1, c} : Finset G).card = 2 := by
      rw [Finset.card_eq_two]; exact ⟨1, c, hc1.symm, rfl⟩
    have := Finset.card_le_card hsub
    omega
  have hxS : x ∈ (S : Subgroup G) := hZS hxZ
  have hcx : c ≠ x := by
    intro h
    have h1 : e ⟨c, hcS⟩ = e ⟨x, hxS⟩ := by
      rw [show (⟨c, hcS⟩ : (S : Subgroup G)) = ⟨x, hxS⟩ from Subtype.ext h]
    refine hxnotR ?_
    rw [← h1, hce]
    exact Work.Dihedral.r_mem_rot _
  have hcases := fourGroup_mem_cases Z hZ hcZ hxZ hc1 hx1 hcx
  obtain ⟨i, hi⟩ := Work.Dihedral.notMem_rot.mp hxnotR
  have hxi : e ⟨x, hxS⟩ = DihedralGroup.sr i := hi
  -- the main computation for a conjugating element `d₀` of `D_n`
  have main : ∀ (d₀ : DihedralGroup n) (ee : ZMod n),
      d₀ * DihedralGroup.sr i * d₀⁻¹ = DihedralGroup.sr ee →
      (MulAut.conj ((e.symm d₀ : (S : Subgroup G)) : G)) • Z = fourOf S n h4 e ee := by
    intro d₀ ee hd₀
    have hdS : ((e.symm d₀ : (S : Subgroup G)) : G) ∈ (S : Subgroup G) := (e.symm d₀).2
    have hde : e ⟨((e.symm d₀ : (S : Subgroup G)) : G), hdS⟩ = d₀ := by
      rw [show (⟨((e.symm d₀ : (S : Subgroup G)) : G), hdS⟩ : (S : Subgroup G)) = e.symm d₀ from
        Subtype.ext rfl, MulEquiv.apply_symm_apply]
    have hcdG : ((e.symm d₀ : (S : Subgroup G)) : G) * c *
        ((e.symm d₀ : (S : Subgroup G)) : G)⁻¹ = c := by
      have hy : ((e.symm d₀ : (S : Subgroup G)) : G) * c *
          ((e.symm d₀ : (S : Subgroup G)) : G)⁻¹ ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hdS hcS)
          ((S : Subgroup G).inv_mem hdS)
      have h2 : (⟨_, hy⟩ : (S : Subgroup G)) = ⟨c, hcS⟩ := by
        apply e.injective
        rw [map_conj_elem S n e hdS hcS hy, hde, hce]
        rw [show d₀ * DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * d₀⁻¹
            = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) from by
          rw [show d₀ * DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * d₀⁻¹
              = (d₀ * DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) * d₀⁻¹ from by group,
            dihedral_r_half_central n heven d₀, mul_assoc, mul_inv_cancel, mul_one]]
      exact congrArg Subtype.val h2
    have hxdG : ((e.symm d₀ : (S : Subgroup G)) : G) * x *
        ((e.symm d₀ : (S : Subgroup G)) : G)⁻¹ = e.symm (DihedralGroup.sr ee) := by
      have hy : ((e.symm d₀ : (S : Subgroup G)) : G) * x *
          ((e.symm d₀ : (S : Subgroup G)) : G)⁻¹ ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hdS hxS)
          ((S : Subgroup G).inv_mem hdS)
      have h2 : (⟨_, hy⟩ : (S : Subgroup G)) = e.symm (DihedralGroup.sr ee) := by
        apply e.injective
        rw [map_conj_elem S n e hdS hxS hy, hde]
        rw [hxi, hd₀, MulEquiv.apply_symm_apply]
      exact congrArg Subtype.val h2
    ext y
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzS : z ∈ (S : Subgroup G) := hZS hz
      have hyS : ((e.symm d₀ : (S : Subgroup G)) : G) * z *
          ((e.symm d₀ : (S : Subgroup G)) : G)⁻¹ ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hdS hzS)
          ((S : Subgroup G).inv_mem hdS)
      simp only [MulAut.smul_def, MulAut.conj_apply]
      rw [mem_fourOf S n h4 e ee hyS]
      rw [map_conj_elem S n e hdS hzS hyS, hde]
      rcases hcases z hz with h | h | h | h
      · rw [show (⟨z, hzS⟩ : (S : Subgroup G)) = 1 from Subtype.ext h, map_one]
        exact (mem_fourEl n heven ee).mpr (Or.inl (by group))
      · rw [show (⟨z, hzS⟩ : (S : Subgroup G)) = ⟨c, hcS⟩ from Subtype.ext h, hce]
        have hgoal : d₀ * DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * d₀⁻¹
            = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
          rw [show d₀ * DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * d₀⁻¹
              = (d₀ * DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) * d₀⁻¹ from by group,
            dihedral_r_half_central n heven d₀, mul_assoc, mul_inv_cancel, mul_one]
        exact (mem_fourEl n heven ee).mpr (Or.inr (Or.inl hgoal))
      · rw [show (⟨z, hzS⟩ : (S : Subgroup G)) = ⟨x, hxS⟩ from Subtype.ext h, hxi, hd₀]
        exact (mem_fourEl n heven ee).mpr (Or.inr (Or.inr (Or.inl rfl)))
      · have hzx : (⟨z, hzS⟩ : (S : Subgroup G)) = ⟨c, hcS⟩ * ⟨x, hxS⟩ :=
          Subtype.ext (by show z = c * x; rw [h])
        rw [hzx, map_mul, hce, hxi]
        have hgoal : d₀ * (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * DihedralGroup.sr i) * d₀⁻¹
            = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * DihedralGroup.sr ee := by
          rw [show d₀ * (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * DihedralGroup.sr i) * d₀⁻¹
              = (d₀ * DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * d₀⁻¹)
                * (d₀ * DihedralGroup.sr i * d₀⁻¹) from by group,
            show d₀ * DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * d₀⁻¹
              = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) from by
              rw [show d₀ * DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * d₀⁻¹
                  = (d₀ * DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) * d₀⁻¹ from by group,
                dihedral_r_half_central n heven d₀, mul_assoc, mul_inv_cancel, mul_one],
            hd₀]
        rw [hgoal]
        exact (mem_fourEl n heven ee).mpr (Or.inr (Or.inr (Or.inr rfl)))
    · intro hy
      have hyS : y ∈ (S : Subgroup G) := fourOf_le S n h4 e ee hy
      rw [mem_fourOf S n h4 e ee hyS] at hy
      rcases hy with h | h | h | h
      · refine ⟨1, Z.one_mem, ?_⟩
        have hy1 : y = 1 := by
          have h2 : (⟨y, hyS⟩ : (S : Subgroup G)) = 1 := by
            apply e.injective
            rw [h, map_one]
          exact Subtype.ext_iff.mp h2
        rw [hy1]
        simp only [MulAut.smul_def, MulAut.conj_apply, mul_one]
        group
      · refine ⟨c, hcZ, ?_⟩
        have hyc : y = c := by
          have h2 : (⟨y, hyS⟩ : (S : Subgroup G)) = ⟨c, hcS⟩ := by
            apply e.injective
            rw [h]
            exact hce.symm
          exact Subtype.ext_iff.mp h2
        rw [hyc]
        simp only [MulAut.smul_def, MulAut.conj_apply]
        exact hcdG
      · refine ⟨x, hxZ, ?_⟩
        have hyx : y = e.symm (DihedralGroup.sr ee) := by
          have h2 : (⟨y, hyS⟩ : (S : Subgroup G)) = e.symm (DihedralGroup.sr ee) := by
            apply e.injective
            rw [h, MulEquiv.apply_symm_apply]
          exact Subtype.ext_iff.mp h2
        rw [hyx]
        simp only [MulAut.smul_def, MulAut.conj_apply]
        exact hxdG
      · refine ⟨c * x, Z.mul_mem hcZ hxZ, ?_⟩
        have hyx : y = c * e.symm (DihedralGroup.sr ee) := by
          have h2 : (⟨y, hyS⟩ : (S : Subgroup G)) = ⟨c, hcS⟩ * e.symm (DihedralGroup.sr ee) := by
            apply e.injective
            rw [h, map_mul, hce, MulEquiv.apply_symm_apply]
          exact Subtype.ext_iff.mp h2
        rw [hyx]
        simp only [MulAut.smul_def, MulAut.conj_apply]
        rw [show ((e.symm d₀ : (S : Subgroup G)) : G) * (c * x) *
            ((e.symm d₀ : (S : Subgroup G)) : G)⁻¹
            = (((e.symm d₀ : (S : Subgroup G)) : G) * c * ((e.symm d₀ : (S : Subgroup G)) : G)⁻¹)
              * (((e.symm d₀ : (S : Subgroup G)) : G) * x
                * ((e.symm d₀ : (S : Subgroup G)) : G)⁻¹) from by group,
          hcdG, hxdG]
  rcases reflection_conj_sr_zero_or_one n h4 i with ⟨d₀, hd₀⟩ | ⟨d₀, hd₀⟩
  · exact Or.inl ⟨_, (e.symm d₀).2, main d₀ 0 hd₀⟩
  · exact Or.inr ⟨_, (e.symm d₀).2, main d₀ 1 hd₀⟩

/-! ## Auxiliary facts: `2`-groups, four-groups, and the central involution -/

/-- A finite group all of whose elements of odd order are trivial is a `2`-group. -/
lemma isPGroup_two_of_forall_odd_orderOf_eq_one {H : Type*} [Group H] [Finite H]
    (h : ∀ x : H, Odd (orderOf x) → x = 1) : IsPGroup 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro x
  have hm0 : orderOf x ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite x)
  have hmult : 2 ^ (orderOf x).factorization 2 *
      (orderOf x / 2 ^ (orderOf x).factorization 2) = orderOf x :=
    Nat.ordProj_mul_ordCompl_eq_self (orderOf x) 2
  have hγm' : (x ^ 2 ^ (orderOf x).factorization 2) ^
      (orderOf x / 2 ^ (orderOf x).factorization 2) = 1 := by
    rw [← pow_mul, hmult, pow_orderOf_eq_one]
  have hγodd : Odd (orderOf (x ^ 2 ^ (orderOf x).factorization 2)) := by
    have hdvd : orderOf (x ^ 2 ^ (orderOf x).factorization 2) ∣
        orderOf x / 2 ^ (orderOf x).factorization 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr hγm'
    have hnodd : Odd (orderOf x / 2 ^ (orderOf x).factorization 2) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact Nat.not_dvd_ordCompl Nat.prime_two hm0
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd] at hnodd ⊢
    intro h2
    exact hnodd (h2.trans hdvd)
  have hγ1 : x ^ 2 ^ (orderOf x).factorization 2 = 1 := h _ hγodd
  exact ⟨(orderOf x).factorization 2,
    Nat.dvd_antisymm (orderOf_dvd_iff_pow_eq_one.mpr hγ1) (Nat.ordProj_dvd (orderOf x) 2)⟩

/-- A four-group is a `2`-group. -/
lemma isPGroup_of_isFourGroup {V : Subgroup G} (hV : Work.GW2.IsFourGroup V) :
    IsPGroup 2 (↥V) :=
  IsPGroup.of_card (p := 2) (n := 2) (by rw [hV.1]; norm_num)

/-- Conjugating a four-group yields a four-group. -/
lemma isFourGroup_smul (f : G ≃* G) {V : Subgroup G} (hV : Work.GW2.IsFourGroup V) :
    Work.GW2.IsFourGroup (f • V) := by
  refine ⟨?_, ?_⟩
  · rw [smul_eq_map, Subgroup.card_map_of_injective f.injective, hV.1]
  · intro v hv
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [MulAut.smul_def, ← map_pow, hV.2 u hu, map_one]

/-- In `DihedralGroup n` with `n ≥ 2`, `r (n/2)` is not the identity. -/
lemma dihedral_half_rot_ne_one (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ≠ 1 := by
  intro h
  have h0 : ((n / 2 : ℕ) : ZMod n) = 0 := DihedralGroup.r.inj h
  have h3 : n ∣ n / 2 := (ZMod.natCast_eq_zero_iff (n / 2) n).mp h0
  have h4 : 0 < n / 2 := by omega
  have h5 : n ≤ n / 2 := Nat.le_of_dvd h4 h3
  omega

/-- In `DihedralGroup n` with `n` even, `r (n/2)` is an involution. -/
lemma dihedral_half_rot_sq (n : ℕ) (heven : Even n) :
    (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ^ 2 = 1 := by
  have hhalf : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
    obtain ⟨r, hr⟩ := heven
    rw [← Nat.cast_add, show n / 2 + n / 2 = n by omega, ZMod.natCast_self]
  rw [sq, DihedralGroup.r_mul_r, hhalf, DihedralGroup.r_zero]

/-- In `DihedralGroup n` with `n ≥ 2` even, `r (n/2)` has order `2`. -/
lemma dihedral_half_rot_orderOf (n : ℕ) [NeZero n] (hn : 2 ≤ n) (heven : Even n) :
    orderOf (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) = 2 := by
  have hdvd : orderOf (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (dihedral_half_rot_sq n heven)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) (dihedral_half_rot_ne_one n hn)
  · exact h

/-- The element of `S` corresponding to `r (n/2)` is an involution. -/
lemma half_rot_involution_sq (S : Sylow 2 G) (n : ℕ) (heven : Even n)
    (e : (S : Subgroup G) ≃* DihedralGroup n) {z : G} (hzS : z ∈ (S : Subgroup G))
    (hze : e ⟨z, hzS⟩ = DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) : z ^ 2 = 1 := by
  have h1 : (⟨z, hzS⟩ : (S : Subgroup G)) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, hze, dihedral_half_rot_sq n heven, map_one]
  have h2 := congrArg (fun y : (S : Subgroup G) => (y : G)) h1
  simpa using h2

/-- The element of `S` corresponding to `r (n/2)` is not the identity (`n ≥ 2`). -/
lemma half_rot_involution_ne_one (S : Sylow 2 G) (n : ℕ) (hn : 2 ≤ n)
    (e : (S : Subgroup G) ≃* DihedralGroup n) {z : G} (hzS : z ∈ (S : Subgroup G))
    (hze : e ⟨z, hzS⟩ = DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) : z ≠ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  intro h
  exact dihedral_half_rot_ne_one n hn (by
    rw [← hze, show (⟨z, hzS⟩ : (S : Subgroup G)) = 1 from Subtype.ext h, map_one])

/-- The element of `S` corresponding to `r (n/2)` has order `2`. -/
lemma half_rot_involution_orderOf (S : Sylow 2 G) (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (e : (S : Subgroup G) ≃* DihedralGroup n) {z : G} (hzS : z ∈ (S : Subgroup G))
    (hze : e ⟨z, hzS⟩ = DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) : orderOf z = 2 := by
  haveI : NeZero n := ⟨by omega⟩
  have hdvd : orderOf z ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (half_rot_involution_sq S n heven e hzS hze)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) (half_rot_involution_ne_one S n hn e hzS hze)
  · exact h

/-- The element of `S` corresponding to `r (n/2)` is central in `S`. -/
lemma half_rot_involution_comm (S : Sylow 2 G) (n : ℕ) [NeZero n] (heven : Even n)
    (e : (S : Subgroup G) ≃* DihedralGroup n) :
    ∀ x ∈ (S : Subgroup G),
      x * ((e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) : (S : Subgroup G)) : G)
        = ((e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) : (S : Subgroup G)) : G) * x := by
  intro x hx
  have h1 : (⟨x, hx⟩ : (S : Subgroup G)) * e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n))
      = e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) * ⟨x, hx⟩ := by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, dihedral_r_half_central n heven]
  have h2 := congrArg (fun y : (S : Subgroup G) => (y : G)) h1
  simpa using h2

/-! ## The "sibling swap" inside the normalizer of a four-group -/

/-- **Sibling swap.**  Let `W ≤ S` be a four-group, `z` the central involution of the dihedral
Sylow subgroup `S` (so `z ∈ W`), and `u ∈ W` with `u ≠ 1`, `u ≠ z`.  Then some element of
`N_G(W)` conjugates `u` to `u * z` and fixes `z`. -/
lemma exists_conj_mem_normalizer_mul_swap (S : Sylow 2 G) (n : ℕ) (hn4 : 4 ≤ n) (h4 : 4 ∣ n)
    (e : (S : Subgroup G) ≃* DihedralGroup n) (W : Subgroup G) (hW : Work.GW2.IsFourGroup W)
    (hWS : W ≤ (S : Subgroup G)) (z : G) (hzW : z ∈ W)
    (hze : e ⟨z, hWS hzW⟩ = DihedralGroup.r ((n / 2 : ℕ) : ZMod n))
    (u : G) (hu : u ∈ W) (hu1 : u ≠ 1) (huz : u ≠ z) :
    ∃ x ∈ Subgroup.normalizer (W : Set G), x * u * x⁻¹ = u * z ∧ x * z * x⁻¹ = z := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have heven : Even n := even_of_four_dvd h4
  have hn : 2 ≤ n := by omega
  have hzS : z ∈ (S : Subgroup G) := hWS hzW
  have huS : u ∈ (S : Subgroup G) := hWS hu
  have hz1 : z ≠ 1 := half_rot_involution_ne_one S n hn e hzS hze
  have hzsq : z * z = 1 := by
    simpa [pow_two] using half_rot_involution_sq S n heven e hzS hze
  -- the corresponding four-group in `DihedralGroup n`
  let V : Subgroup (DihedralGroup n) := (W.subgroupOf (S : Subgroup G)).map e.toMonoidHom
  have hV : Work.GW2.IsFourGroup V := by
    refine ⟨?_, ?_⟩
    · show Nat.card V = 4
      rw [Subgroup.card_map_of_injective e.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWS).toEquiv]
      exact hW.1
    · intro v hv
      obtain ⟨y, hy, hyv⟩ := Subgroup.mem_map.mp hv
      rw [← hyv, ← map_pow]
      have h2 : y ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hW.2 (y : G) (Subgroup.mem_subgroupOf.mp hy)
      rw [h2, map_one]
  have huV : e ⟨u, huS⟩ ∈ V :=
    Subgroup.mem_map.mpr ⟨⟨u, huS⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  have huV1 : e ⟨u, huS⟩ ≠ 1 := by
    intro h
    have h1 : e (1 : (S : Subgroup G)) = e ⟨u, huS⟩ := by rw [map_one, h]
    exact hu1 (Subtype.ext_iff.mp (e.injective h1).symm)
  have huVz : e ⟨u, huS⟩ ≠ DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
    intro h
    have h1 : e ⟨z, hzS⟩ = e ⟨u, huS⟩ := by rw [hze, h]
    exact huz (Subtype.ext_iff.mp (e.injective h1)).symm
  obtain ⟨s, hsrot, hs⟩ :=
    DihedralFacts.exists_conj_reflection_swap n h4 V hV (e ⟨u, huS⟩) huV huV1 huVz
  obtain ⟨t, rfl⟩ := Work.Dihedral.mem_rot.mp hsrot
  -- the conjugating element of `S`
  set x : G := ((e.symm (DihedralGroup.r t) : (S : Subgroup G)) : G) with hxdef
  have hxS : x ∈ (S : Subgroup G) := (e.symm (DihedralGroup.r t)).2
  have hxe : e ⟨x, hxS⟩ = DihedralGroup.r t := by
    rw [show (⟨x, hxS⟩ : (S : Subgroup G)) = e.symm (DihedralGroup.r t) from Subtype.ext rfl,
      MulEquiv.apply_symm_apply]
  have hA : x * u * x⁻¹ = u * z := by
    have hmem : x * u * x⁻¹ ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hxS huS)
        ((S : Subgroup G).inv_mem hxS)
    have hmem2 : u * z ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem huS hzS
    have key : (⟨x * u * x⁻¹, hmem⟩ : (S : Subgroup G)) = ⟨u * z, hmem2⟩ := by
      apply e.injective
      rw [map_conj_elem S n e hxS huS hmem, hxe, hs]
      rw [show e ⟨u, huS⟩ * DihedralGroup.r ((n / 2 : ℕ) : ZMod n)
          = e ⟨u, huS⟩ * e ⟨z, hzS⟩ from by rw [hze], ← map_mul]
      rfl
    exact congrArg (fun y : (S : Subgroup G) => (y : G)) key
  have hB : x * z * x⁻¹ = z := by
    have hmem : x * z * x⁻¹ ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hxS hzS)
        ((S : Subgroup G).inv_mem hxS)
    have key : (⟨x * z * x⁻¹, hmem⟩ : (S : Subgroup G)) = ⟨z, hzS⟩ := by
      apply e.injective
      rw [map_conj_elem S n e hxS hzS hmem, hxe, hze]
      rw [show DihedralGroup.r t * DihedralGroup.r ((n / 2 : ℕ) : ZMod n)
            * (DihedralGroup.r t)⁻¹ = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) from by
        rw [dihedral_r_half_central n heven (DihedralGroup.r t), mul_assoc, mul_inv_cancel,
          mul_one]]
    exact congrArg (fun y : (S : Subgroup G) => (y : G)) key
  have hxN : x ∈ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨v, hv, rfl⟩ := hy
      change (MulAut.conj x) v ∈ W
      rw [MulAut.conj_apply]
      rcases fourGroup_mem_cases W hW hzW hu hz1 hu1 (Ne.symm huz) v hv with h | h | h | h
      · rw [h]; simp
      · rw [h, hB]; exact hzW
      · rw [h, hA]; exact W.mul_mem hu hzW
      · rw [h]
        rw [show x * (z * u) * x⁻¹ = (x * z * x⁻¹) * (x * u * x⁻¹) from by group, hB, hA,
          show z * (u * z) = (z * u) * z from by group,
          show z * u = u * z from fourGroup_comm W hW hzW hu, mul_assoc, hzsq, mul_one]
        exact hu
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  exact ⟨x, hxN, hA, hB⟩

/-! ## Conjugation bookkeeping for subgroups -/

/-- Two successive conjugations. -/
lemma conj_smul_conj_smul (a b : G) (U : Subgroup G) :
    (MulAut.conj a) • ((MulAut.conj b) • U) = (MulAut.conj (a * b)) • U := by
  rw [← mul_smul, map_mul]

/-- `S`-conjugacy of subgroups is transitive. -/
lemma conj_smul_trans (S : Subgroup G) {U V Wv : Subgroup G}
    (h₁ : ∃ d ∈ S, (MulAut.conj d) • U = V) (h₂ : ∃ d ∈ S, (MulAut.conj d) • V = Wv) :
    ∃ d ∈ S, (MulAut.conj d) • U = Wv := by
  obtain ⟨a, ha, ha'⟩ := h₁
  obtain ⟨b, hb, hb'⟩ := h₂
  refine ⟨b * a, S.mul_mem hb ha, ?_⟩
  rw [← hb', ← ha', ← conj_smul_conj_smul b a U]

/-- `S`-conjugacy of subgroups is symmetric. -/
lemma conj_smul_symm (S : Subgroup G) {U V : Subgroup G}
    (h : ∃ d ∈ S, (MulAut.conj d) • U = V) : ∃ d ∈ S, (MulAut.conj d) • V = U := by
  obtain ⟨a, ha, ha'⟩ := h
  refine ⟨a⁻¹, S.inv_mem ha, ?_⟩
  rw [← ha', ← mul_smul, map_inv, inv_mul_cancel, one_smul]

/-- Membership in a conjugate subgroup. -/
lemma mem_conj_smul_iff (γ : G) (U : Subgroup G) (x : G) :
    x ∈ (MulAut.conj γ) • U ↔ γ⁻¹ * x * γ ∈ U := by
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨u, hu, hu'⟩
    rw [MulAut.smul_def, MulAut.conj_apply] at hu'
    rw [← hu', show γ⁻¹ * (γ * u * γ⁻¹) * γ = u from by group]
    exact hu
  · intro hx
    exact ⟨γ⁻¹ * x * γ, hx, by rw [MulAut.smul_def, MulAut.conj_apply]; group⟩

/-! ## Every four-group can be conjugated into `S` -/

/-- Any four-group of `G` is conjugate into a given dihedral Sylow `2`-subgroup. -/
lemma exists_conj_le_sylow_of_fourGroup (S : Sylow 2 G) (n : ℕ) (hn : 2 ≤ n)
    (hiso : Nonempty ((S : Subgroup G) ≃* DihedralGroup n))
    (hconj : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (U : Subgroup G) (hU : Work.GW2.IsFourGroup U) :
    ∃ γ : G, (MulAut.conj γ) • U ≤ (S : Subgroup G) := by
  classical
  obtain ⟨e⟩ := hiso
  have hcardS : Nat.card (S : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have heven : Even n := even_of_two_mul_eq_two_pow hn (by rw [← hcardS, hk])
  haveI : NeZero n := ⟨by omega⟩
  let z : G := ((e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) : (S : Subgroup G)) : G)
  have hzS : z ∈ (S : Subgroup G) := (e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n))).2
  have hze : e ⟨z, hzS⟩ = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
    rw [show (⟨z, hzS⟩ : (S : Subgroup G)) = e.symm (DihedralGroup.r _) from Subtype.ext rfl,
      MulEquiv.apply_symm_apply]
  have hz2 : orderOf z = 2 := half_rot_involution_orderOf S n hn heven e hzS hze
  have hzc : ∀ x ∈ (S : Subgroup G), x * z = z * x := half_rot_involution_comm S n heven e
  obtain ⟨u, huU, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra h
    push_neg at h
    haveI : Fintype U := Fintype.ofFinite U
    have hcard : Fintype.card U = 4 := by rw [← Nat.card_eq_fintype_card]; exact hU.1
    have hsub : (Finset.univ : Finset U).image Subtype.val ⊆ ({1} : Finset G) := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      simp [h a a.2]
    have h1 : ((Finset.univ : Finset U).image Subtype.val).card = 4 := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ, hcard]
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hu2 : orderOf u = 2 := fourGroup_orderOf U hU huU hu1
  obtain ⟨g, hg⟩ := isConj_iff.mp (hconj u z hu2 hz2)
  have hU' : Work.GW2.IsFourGroup ((MulAut.conj g) • U) := isFourGroup_smul (MulAut.conj g) hU
  have hzU' : z ∈ (MulAut.conj g) • U :=
    (Subgroup.mem_smul_pointwise_iff_exists z (MulAut.conj g) U).mpr
      ⟨u, huU, by rw [MulAut.smul_def, MulAut.conj_apply, hg]⟩
  have hQc : (MulAut.conj g) • U ≤ Subgroup.centralizer ({z} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact fourGroup_comm _ hU' hzU' hy
  obtain ⟨x, -, hxle⟩ := conj_le_sylow_of_mem_centralizer S z hzc _
    (isPGroup_of_isFourGroup hU') hQc
  refine ⟨x * g, ?_⟩
  rw [show MulAut.conj (x * g) = MulAut.conj x * MulAut.conj g from map_mul MulAut.conj x g,
    mul_smul]
  intro y hy
  rw [Subgroup.mem_smul_pointwise_iff_exists] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  change x * v * x⁻¹ ∈ (S : Subgroup G)
  exact hxle v hv

/-! ## The four-groups of a dihedral `2`-group -/

/-- If `W` and `Z₁` are four-groups of `S` that are not `S`-conjugate, then every four-group of
`S` is `S`-conjugate to one of them (there are at most two classes, and `W`, `Z₁` lie in
different ones). -/
lemma fourGroup_sylow_conj_or (S : Sylow 2 G) (n : ℕ) (hn4 : 4 ≤ n) (h4 : 4 ∣ n)
    (e : (S : Subgroup G) ≃* DihedralGroup n)
    (W Z₁ : Subgroup G) (hW : Work.GW2.IsFourGroup W) (hWS : W ≤ (S : Subgroup G))
    (hZ₁ : Work.GW2.IsFourGroup Z₁) (hZ₁S : Z₁ ≤ (S : Subgroup G))
    (hnotconj : ¬ ∃ d ∈ (S : Subgroup G), (MulAut.conj d) • W = Z₁) :
    ∀ U : Subgroup G, Work.GW2.IsFourGroup U → U ≤ (S : Subgroup G) →
      (∃ d ∈ (S : Subgroup G), (MulAut.conj d) • U = W) ∨
        ∃ d ∈ (S : Subgroup G), (MulAut.conj d) • U = Z₁ := by
  have hsame : ∀ (V V' : Subgroup G) (i : ZMod n),
      (∃ d ∈ (S : Subgroup G), (MulAut.conj d) • V = fourOf S n h4 e i) →
      (∃ d ∈ (S : Subgroup G), (MulAut.conj d) • V' = fourOf S n h4 e i) →
      ∃ d ∈ (S : Subgroup G), (MulAut.conj d) • V' = V :=
    fun V V' i hV hV' => conj_smul_trans _ hV' (conj_smul_symm _ hV)
  have hWc := fourGroup_conj_fourOf S n hn4 h4 e W hW hWS
  have hZc := fourGroup_conj_fourOf S n hn4 h4 e Z₁ hZ₁ hZ₁S
  intro U hU hUS
  rcases hWc with hW0 | hW1 <;> rcases hZc with hZ0 | hZ1
  · exact absurd (conj_smul_symm _ (hsame W Z₁ 0 hW0 hZ0)) hnotconj
  · rcases fourGroup_conj_fourOf S n hn4 h4 e U hU hUS with hU0 | hU1
    · exact Or.inl (hsame W U 0 hW0 hU0)
    · exact Or.inr (hsame Z₁ U 1 hZ1 hU1)
  · rcases fourGroup_conj_fourOf S n hn4 h4 e U hU hUS with hU0 | hU1
    · exact Or.inr (hsame Z₁ U 0 hZ0 hU0)
    · exact Or.inl (hsame W U 1 hW1 hU1)
  · exact absurd (conj_smul_symm _ (hsame W Z₁ 1 hW1 hZ1)) hnotconj

/-! ## Quotients of the normalizer by the centralizer -/

/-- `DihedralGroup 2` has exponent `2`. -/
lemma dihedral_two_sq_one (y : DihedralGroup 2) : y ^ 2 = 1 := by
  rcases Work.Dihedral.eq_r_or_sr y with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [sq, DihedralGroup.r_mul_r]
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
    have hii : i + i = (0 : ZMod 2) := by
      calc i + i = 2 * i := by ring
        _ = ((2 : ℕ) : ZMod 2) * i := by norm_num
        _ = 0 := by rw [h2, zero_mul]
    rw [hii, DihedralGroup.r_zero]
  · rw [sq, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]

lemma dihedral_sq_one_of_eq_two {m : ℕ} (hm : m = 2) (y : DihedralGroup m) : y ^ 2 = 1 := by
  cases hm
  exact dihedral_two_sq_one y

/-- If the automorphism group of `X` is a `2`-group then so is `N_G(X)/C_G(X)`. -/
lemma isPGroup_quotient_of_mulAut_isPGroup (X : Subgroup G) [Finite ↥X]
    (hAut : IsPGroup 2 (MulAut ↥X)) :
    IsPGroup 2 (↥(Subgroup.normalizer (X : Set G)) ⧸
      (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
  haveI : Finite ↥(Subgroup.normalizer (X : Set G)) := Subtype.finite
  let φ : ↥(Subgroup.normalizer (X : Set G)) →* MulAut ↥X := X.normalizerMonoidHom
  have hker := X.normalizerMonoidHom_ker
  have hrange : IsPGroup 2 (↥φ.range) :=
    hAut.of_injective (Subgroup.subtype φ.range) Subtype.coe_injective
  have hq : IsPGroup 2 (↥(Subgroup.normalizer (X : Set G)) ⧸ φ.ker) :=
    hrange.of_equiv (QuotientGroup.quotientKerEquivRange φ).symm
  exact hq.of_equiv (QuotientGroup.quotientMulEquivOfEq hker)

/-- For a four-group `X` with `N_G(X) ≤ C_G(c)` for some non-identity `c ∈ X`, the quotient
`N_G(X)/C_G(X)` is a `2`-group: every induced automorphism fixes `c`, hence is an involution. -/
lemma isPGroup_quotient_centralizer_of_fourGroup (X : Subgroup G) (hX : Work.GW2.IsFourGroup X)
    (c : G) (hcX : c ∈ X) (hc1 : c ≠ 1)
    (hNC : Subgroup.normalizer (X : Set G) ≤ Subgroup.centralizer ({c} : Set G)) :
    IsPGroup 2 (↥(Subgroup.normalizer (X : Set G)) ⧸
      (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
  classical
  haveI : Finite ↥X := Subtype.finite
  haveI : Finite ↥(Subgroup.normalizer (X : Set G)) := Subtype.finite
  let φ : ↥(Subgroup.normalizer (X : Set G)) →* MulAut ↥X := X.normalizerMonoidHom
  have hker := X.normalizerMonoidHom_ker
  have hodd : ∀ σ : ↥φ.range, Odd (orderOf σ) → σ = 1 := by
    rintro ⟨σ, hσ⟩ hσodd
    rw [Subgroup.orderOf_mk] at hσodd
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hσ
    have hfix : σ ⟨c, hcX⟩ = ⟨c, hcX⟩ := by
      have h1 : φ n ⟨c, hcX⟩ = ⟨c, hcX⟩ := by
        have h2 : (n : G) * c * (n : G)⁻¹ = c := by
          have h3 := Subgroup.mem_centralizer_iff.mp (hNC n.2) c (Set.mem_singleton c)
          rw [← h3, mul_assoc, mul_inv_cancel, mul_one]
        apply Subtype.ext
        show (n : G) * c * (n : G)⁻¹ = c
        exact h2
      rw [← hn, h1]
    have hsq : ∀ v : ↥X, v ^ 2 = 1 := fun v => Subtype.ext (by
      show (v : G) ^ 2 = (1 : G)
      exact hX.2 (v : G) v.2)
    have hβ := AutFacts.mulAut_fourGroup_eq_one_of_odd (V := ↥X) hX.1 hsq ⟨c, hcX⟩
      (fun h => hc1 (Subtype.ext_iff.mp h)) σ hfix hσodd
    exact Subtype.ext hβ
  have hrange : IsPGroup 2 (↥φ.range) := isPGroup_two_of_forall_odd_orderOf_eq_one hodd
  have hq : IsPGroup 2 (↥(Subgroup.normalizer (X : Set G)) ⧸ φ.ker) :=
    hrange.of_equiv (QuotientGroup.quotientKerEquivRange φ).symm
  exact hq.of_equiv (QuotientGroup.quotientMulEquivOfEq hker)

/-- **The `N/C`-condition for all `2`-subgroups**, given that every four-group of `G` is
conjugate to the single four-group `W` whose normalizer is contained in `C_G(c)`. -/
lemma isPGroup_quotient_centralizer_of_twoGroup (S : Sylow 2 G) (n : ℕ) (hn : 2 ≤ n)
    (hiso : Nonempty ((S : Subgroup G) ≃* DihedralGroup n))
    (W : Subgroup G) (hW : Work.GW2.IsFourGroup W) (cW : G) (hcW : cW ∈ W) (hcW1 : cW ≠ 1)
    (hNC : Subgroup.normalizer (W : Set G) ≤ Subgroup.centralizer ({cW} : Set G))
    (hallconj : ∀ U : Subgroup G, Work.GW2.IsFourGroup U → ∃ γ : G, (MulAut.conj γ) • U = W) :
    ∀ X : Subgroup G, IsPGroup 2 X →
      IsPGroup 2 (↥(Subgroup.normalizer (X : Set G)) ⧸
        (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
  intro X hX
  by_cases hfour : ∃ γ : G, (MulAut.conj γ) • X = W
  · obtain ⟨γ, hγ⟩ := hfour
    have hX' : X = (MulAut.conj γ⁻¹) • W := by
      rw [← hγ, ← mul_smul, map_inv, inv_mul_cancel, one_smul]
    have hXfour : Work.GW2.IsFourGroup X := by
      rw [hX']; exact isFourGroup_smul (MulAut.conj γ⁻¹) hW
    have hcX : γ⁻¹ * cW * γ ∈ X := by
      rw [hX', mem_conj_smul_iff]
      convert hcW using 1
      group
    have hcX1 : γ⁻¹ * cW * γ ≠ 1 := by
      intro h
      exact hcW1 (by
        have h1 : cW = γ * (γ⁻¹ * cW * γ) * γ⁻¹ := by group
        rw [h1, h]
        group)
    have hXW : ∀ x : G, x ∈ X ↔ γ * x * γ⁻¹ ∈ W := by
      intro x
      have h := mem_conj_smul_iff γ⁻¹ W x
      rw [← hX'] at h
      simpa [inv_inv] using h
    have hWX : ∀ x : G, x ∈ W ↔ γ⁻¹ * x * γ ∈ X := by
      intro x
      have h := (hXW (γ⁻¹ * x * γ)).symm
      have h2 : γ * (γ⁻¹ * x * γ) * γ⁻¹ = x := by group
      rwa [h2] at h
    have hNCX : Subgroup.normalizer (X : Set G) ≤
        Subgroup.centralizer ({γ⁻¹ * cW * γ} : Set G) := by
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      have hnW : γ * n * γ⁻¹ ∈ Subgroup.normalizer (W : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro u
        have h1 : u ∈ W ↔ γ⁻¹ * u * γ ∈ X := hWX u
        have h2 : γ⁻¹ * u * γ ∈ X ↔ n * (γ⁻¹ * u * γ) * n⁻¹ ∈ X :=
          Subgroup.mem_normalizer_iff.mp hn (γ⁻¹ * u * γ)
        have h3 : n * (γ⁻¹ * u * γ) * n⁻¹ ∈ X ↔
            γ * (n * (γ⁻¹ * u * γ) * n⁻¹) * γ⁻¹ ∈ W := hXW _
        have h4 : (γ * (n * (γ⁻¹ * u * γ) * n⁻¹) * γ⁻¹ ∈ W) ↔
            ((γ * n * γ⁻¹) * u * (γ * n * γ⁻¹)⁻¹ ∈ W) := by
          constructor <;> intro h <;> convert h using 1 <;> group
        exact h1.trans (h2.trans (h3.trans h4))
      have h6 : cW * (γ * n * γ⁻¹) = (γ * n * γ⁻¹) * cW :=
        Subgroup.mem_centralizer_iff.mp (hNC hnW) cW (Set.mem_singleton cW)
      have h7 : (γ⁻¹ * cW * γ) * n = n * (γ⁻¹ * cW * γ) := by
        have h8 : γ⁻¹ * (cW * (γ * n * γ⁻¹)) * γ = γ⁻¹ * ((γ * n * γ⁻¹) * cW) * γ := by
          rw [h6]
        convert h8 using 1 <;> group
      exact h7
    exact isPGroup_quotient_centralizer_of_fourGroup X hXfour _ hcX hcX1 hNCX
  · rcases DihedralSylow.subgroup_cyclic_or_dihedral S n hn hiso X hX with hcyc | ⟨m, hm2, hem⟩
    · haveI : Finite ↥X := Subtype.finite
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
      exact isPGroup_quotient_of_mulAut_isPGroup X (isPGroup_mulAut_cyclic hcyc k hk)
    · obtain ⟨em⟩ := hem
      haveI : Finite ↥X := Subtype.finite
      have hcardX : Nat.card ↥X = 2 * m := by
        rw [Nat.card_congr em.toEquiv, DihedralGroup.nat_card]
      have hm3 : 3 ≤ m := by
        by_contra h
        have hm : m = 2 := by omega
        have hXfour : Work.GW2.IsFourGroup X := by
          refine ⟨?_, ?_⟩
          · rw [hcardX, hm]
          · intro x hx
            have h1 : (⟨x, hx⟩ : ↥X) ^ 2 = 1 := by
              apply em.injective
              rw [map_pow, dihedral_sq_one_of_eq_two hm, map_one]
            have h2 := congrArg (fun y : ↥X => (y : G)) h1
            simpa using h2
        exact hfour (hallconj X hXfour)
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
      have hk2 : 2 ≤ k := by
        have h : 2 * m = 2 ^ k := by rw [← hcardX, hk]
        by_contra hk'
        have h1 : k ≤ 1 := by omega
        interval_cases k
        · rw [pow_zero] at h; omega
        · rw [pow_one] at h; omega
      have hmk : m = 2 ^ (k - 1) := by
        have h : 2 * m = 2 ^ k := by rw [← hcardX, hk]
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [pow_succ'] at h
        have h2 : m = 2 ^ k' := Nat.mul_left_cancel (by norm_num) h
        rw [h2]
        congr 1
      have hj : 2 ≤ k - 1 := by
        by_contra h
        rcases (by omega : k - 1 = 0 ∨ k - 1 = 1) with h1 | h1
        · rw [h1, pow_zero] at hmk; omega
        · rw [h1, pow_one] at hmk; omega
      rw [hmk] at em
      exact isPGroup_quotient_of_mulAut_isPGroup X
        ((isPGroup_mulAut_dihedral (k - 1) hj).of_equiv (MulAut.congr em).symm)

/-- Conjugating a normalizer: an element normalizing `γ H γ⁻¹` has its `γ`-conjugate in
`N_G(H)`. -/
lemma mem_normalizer_conj_smul_inv (γ : G) (H : Subgroup G) {n : G}
    (hn : n ∈ Subgroup.normalizer ((MulAut.conj γ) • H : Set G)) :
    γ⁻¹ * n * γ ∈ Subgroup.normalizer (H : Set G) := by
  have hmem : (MulAut.conj γ⁻¹) n ∈
      (Subgroup.normalizer ((MulAut.conj γ) • H : Set G)).map
        (MulAut.conj γ⁻¹).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
  have hle := Subgroup.le_normalizer_map (f := (MulAut.conj γ⁻¹).toMonoidHom)
    (H := (MulAut.conj γ) • H)
  have h2 := hle hmem
  rw [← smul_eq_map (MulAut.conj γ⁻¹) ((MulAut.conj γ) • H), ← mul_smul, ← map_mul,
    inv_mul_cancel, map_one, one_smul] at h2
  rwa [MulAut.conj_apply, inv_inv] at h2

/-- If `W`, `Z₁` are four-groups of `S` that are not `S`-conjugate (and `W` is `G`-conjugate to
`Z₁`), then every four-group of `G` is `G`-conjugate to `W`. -/
lemma fourGroup_conj_all_of_not_conj (S : Sylow 2 G) (n : ℕ) (hn4 : 4 ≤ n) (h4 : 4 ∣ n)
    (e : (S : Subgroup G) ≃* DihedralGroup n)
    (hconj : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (W Z₁ : Subgroup G) (hW : Work.GW2.IsFourGroup W) (hWS : W ≤ (S : Subgroup G))
    (hZ₁ : Work.GW2.IsFourGroup Z₁) (hZ₁S : Z₁ ≤ (S : Subgroup G))
    (hWZ₁ : ∃ γ : G, (MulAut.conj γ) • W = Z₁)
    (hnotconj : ¬ ∃ d ∈ (S : Subgroup G), (MulAut.conj d) • W = Z₁) :
    ∀ U : Subgroup G, Work.GW2.IsFourGroup U → ∃ γ : G, (MulAut.conj γ) • U = W := by
  intro U hU
  obtain ⟨γ₀, hγ₀⟩ := exists_conj_le_sylow_of_fourGroup S n (by omega) ⟨e⟩ hconj U hU
  have hY : Work.GW2.IsFourGroup ((MulAut.conj γ₀) • U) := isFourGroup_smul (MulAut.conj γ₀) hU
  rcases fourGroup_sylow_conj_or S n hn4 h4 e W Z₁ hW hWS hZ₁ hZ₁S hnotconj
      ((MulAut.conj γ₀) • U) hY hγ₀ with ⟨d, hdS, hd⟩ | ⟨d, hdS, hd⟩
  · exact ⟨d * γ₀, by rw [← conj_smul_conj_smul d γ₀ U, hd]⟩
  · obtain ⟨δ, hδ⟩ := hWZ₁
    refine ⟨δ⁻¹ * d * γ₀, ?_⟩
    have hYeq : (MulAut.conj (d⁻¹ * δ)) • W = (MulAut.conj γ₀) • U := by
      rw [← conj_smul_conj_smul d⁻¹ δ W, hδ, ← hd,
        conj_smul_conj_smul d⁻¹ d ((MulAut.conj γ₀) • U),
        show d⁻¹ * d = 1 from by group, map_one, one_smul]
    rw [← conj_smul_conj_smul (δ⁻¹ * d) γ₀ U, ← hYeq,
      conj_smul_conj_smul (δ⁻¹ * d) (d⁻¹ * δ) W,
      show (δ⁻¹ * d) * (d⁻¹ * δ) = 1 from by group, map_one, one_smul]

/-- **There is no "bad configuration"** for `n ≥ 4`: if `W ≤ S` is a four-group and some
`w ∈ W#` has `N_G(W) ≤ C_G(w)`, then `G` has a normal subgroup of index `2`. -/
theorem no_bad_config_of_four_le (S : Sylow 2 G) (n : ℕ) (hn4 : 4 ≤ n) (h4 : 4 ∣ n)
    (hiso : Nonempty ((S : Subgroup G) ≃* DihedralGroup n))
    (hnoN : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hconj : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (W : Subgroup G) (hW : Work.GW2.IsFourGroup W) (hWS : W ≤ (S : Subgroup G))
    (w : G) (hw : w ∈ W) (hw1 : w ≠ 1)
    (hbad : Subgroup.normalizer (W : Set G) ≤ Subgroup.centralizer ({w} : Set G)) : False := by
  classical
  obtain ⟨e⟩ := hiso
  have hn2 : 2 ≤ n := by omega
  have heven : Even n := even_of_four_dvd h4
  haveI : NeZero n := ⟨by omega⟩
  let z : G := ((e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) : (S : Subgroup G)) : G)
  have hzS : z ∈ (S : Subgroup G) := (e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n))).2
  have hze : e ⟨z, hzS⟩ = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
    rw [show (⟨z, hzS⟩ : (S : Subgroup G)) = e.symm (DihedralGroup.r _) from Subtype.ext rfl,
      MulEquiv.apply_symm_apply]
  have hzW : z ∈ W := fourOf_center_mem S n hn4 h4 e W hW hWS
  have hz1 : z ≠ 1 := half_rot_involution_ne_one S n hn2 e hzS hze
  have hz2 : orderOf z = 2 := half_rot_involution_orderOf S n hn2 heven e hzS hze
  have hzc : ∀ x ∈ (S : Subgroup G), x * z = z * x := half_rot_involution_comm S n heven e
  -- **Step 1**: `hbad` forces `w = z`
  have hbadc : Subgroup.normalizer (W : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
    have hwz : w = z := by
      by_contra hwz
      obtain ⟨u, hu, hu1, huw, huz, -⟩ := fourGroup_third W hW hw hw1 hzW hz1 hwz
      have hwzu : w = z * u := by
        rcases fourGroup_mem_cases W hW hzW hu hz1 hu1 (Ne.symm huz) w hw with h | h | h | h
        · exact absurd h hw1
        · exact absurd h hwz
        · exact absurd h.symm huw
        · exact h
      have huzw : u * z = w := by rw [fourGroup_comm W hW hu hzW, ← hwzu]
      obtain ⟨x, hxN, hxu, -⟩ :=
        exists_conj_mem_normalizer_mul_swap S n hn4 h4 e W hW hWS z hzW hze u hu hu1 huz
      have hxw : x * w * x⁻¹ = w := by
        have h3 := Subgroup.mem_centralizer_iff.mp (hbad hxN) w (Set.mem_singleton w)
        rw [← h3, mul_assoc, mul_inv_cancel, mul_one]
      have huw' : u = w := by
        have h4 : x * u * x⁻¹ = x * w * x⁻¹ := by rw [hxu, huzw, hxw]
        exact mul_left_cancel (mul_right_cancel h4)
      exact huw huw'
    rw [hwz] at hbad
    exact hbad
  -- **Step 3**: conjugate an element of `W#` to `z` and move the conjugate of `W` into `S`
  obtain ⟨u, hu, hu1, huz⟩ : ∃ u ∈ W, u ≠ 1 ∧ u ≠ z := by
    by_contra h
    push_neg at h
    haveI : Fintype W := Fintype.ofFinite W
    have hcard : Fintype.card W = 4 := by rw [← Nat.card_eq_fintype_card]; exact hW.1
    have hsub : (Finset.univ : Finset W).image Subtype.val ⊆ ({1, z} : Finset G) := by
      intro a ha
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ha
      by_cases h1 : (b : G) = 1
      · simp [h1]
      · have h2 := h b b.2 h1
        simp [h2]
    have h1 : ((Finset.univ : Finset W).image Subtype.val).card = 4 := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ, hcard]
    have h2 : ({1, z} : Finset G).card = 2 := by
      rw [Finset.card_eq_two]; exact ⟨1, z, hz1.symm, rfl⟩
    have := Finset.card_le_card hsub
    omega
  obtain ⟨g, hg⟩ := isConj_iff.mp (hconj u z (fourGroup_orderOf W hW hu hu1) hz2)
  have hU' : Work.GW2.IsFourGroup ((MulAut.conj g) • W) := isFourGroup_smul (MulAut.conj g) hW
  have hzU' : z ∈ (MulAut.conj g) • W :=
    (Subgroup.mem_smul_pointwise_iff_exists z (MulAut.conj g) W).mpr
      ⟨u, hu, by rw [MulAut.smul_def, MulAut.conj_apply, hg]⟩
  have hQc : (MulAut.conj g) • W ≤ Subgroup.centralizer ({z} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact fourGroup_comm _ hU' hzU' hy
  obtain ⟨xx, hxxC, hxxle⟩ := conj_le_sylow_of_mem_centralizer S z hzc _
    (isPGroup_of_isFourGroup hU') hQc
  set Z₁ : Subgroup G := (MulAut.conj (xx * g)) • W with hZ₁def
  have hZ₁S : Z₁ ≤ (S : Subgroup G) := by
    rw [hZ₁def, show MulAut.conj (xx * g) = MulAut.conj xx * MulAut.conj g from
      map_mul MulAut.conj xx g, mul_smul]
    intro y hy
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    change xx * v * xx⁻¹ ∈ (S : Subgroup G)
    exact hxxle v hv
  have hZ₁four : Work.GW2.IsFourGroup Z₁ := by
    rw [hZ₁def]; exact isFourGroup_smul (MulAut.conj (xx * g)) hW
  have hWZ₁ : ∃ γ : G, (MulAut.conj γ) • W = Z₁ := ⟨xx * g, hZ₁def.symm⟩
  -- **Steps 3/4**: the dichotomy
  by_cases hcaseA : ∃ d ∈ (S : Subgroup G), (MulAut.conj d) • W = Z₁
  · obtain ⟨d, hdS, hd⟩ := hcaseA
    have hhW : (MulAut.conj (d⁻¹ * (xx * g))) • W = W := by
      rw [← conj_smul_conj_smul d⁻¹ (xx * g) W, ← hZ₁def, ← hd, ← mul_smul, map_inv,
        inv_mul_cancel, one_smul]
    have hhN : d⁻¹ * (xx * g) ∈ Subgroup.normalizer (W : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      show (MulAut.conj (d⁻¹ * (xx * g))) • W = W
      exact hhW
    have hzu : xx * (g * u * g⁻¹) * xx⁻¹ = z := by
      rw [hg]
      have h := Subgroup.mem_centralizer_iff.mp hxxC z (Set.mem_singleton z)
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    have hhu : (d⁻¹ * (xx * g)) * u * (d⁻¹ * (xx * g))⁻¹ = z := by
      rw [show (d⁻¹ * (xx * g)) * u * (d⁻¹ * (xx * g))⁻¹
          = d⁻¹ * ((xx * g) * u * (xx * g)⁻¹) * d from by group,
        show (xx * g) * u * (xx * g)⁻¹ = xx * (g * u * g⁻¹) * xx⁻¹ from by group, hzu,
        show d⁻¹ * z * d = z from by
          rw [show d⁻¹ * z * d = d⁻¹ * (z * d) from by group, ← hzc d hdS]
          group]
    have hhz : (d⁻¹ * (xx * g)) * z * (d⁻¹ * (xx * g))⁻¹ = z := by
      have h := Subgroup.mem_centralizer_iff.mp (hbadc hhN) z (Set.mem_singleton z)
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    have huz' : u = z := by
      have h4 : (d⁻¹ * (xx * g)) * u * (d⁻¹ * (xx * g))⁻¹
          = (d⁻¹ * (xx * g)) * z * (d⁻¹ * (xx * g))⁻¹ := by rw [hhu, hhz]
      exact mul_left_cancel (mul_right_cancel h4)
    exact huz huz'
  · -- **Steps 5--7**: the global argument
    have hallconj : ∀ U : Subgroup G, Work.GW2.IsFourGroup U → ∃ γ : G, (MulAut.conj γ) • U = W :=
      fourGroup_conj_all_of_not_conj S n hn4 h4 e hconj W Z₁ hW hWS hZ₁four hZ₁S hWZ₁ hcaseA
    have hN2 := isPGroup_quotient_centralizer_of_twoGroup S n hn2 ⟨e⟩ W hW z hzW hz1 hbadc
      hallconj
    have hHPC :=
      (OddOrder.Isaacs.Ch05.hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer
        (G := G) (p := 2)).mpr hN2
    obtain ⟨N, hNnorm, hNcomp⟩ := hHPC
    obtain ⟨M, hMnorm, hMidx⟩ := normal_index_two_of_complement N hNnorm S n hn2 ⟨e⟩ (hNcomp S)
    exact hnoN M hMnorm hMidx

/-- **The last sentence of Gorenstein 7.7.3 / Bender 1.6**: in a group with dihedral Sylow
`2`-subgroup in which all involutions are conjugate, the normalizer of a four-group acts
transitively on its non-identity elements. -/
theorem fourGroup_normalizer_transitive {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (n : ℕ) (hn : 2 ≤ n) (hiso : Nonempty ((S : Subgroup G) ≃* DihedralGroup n))
    (hnoN : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hconj : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (V : Subgroup G) (hV : Work.GW2.IsFourGroup V) (x : G) (hx : x ∈ V) (hx1 : x ≠ 1)
    (y : G) (hy : y ∈ V) (hy1 : y ≠ 1) :
    ∃ g ∈ Subgroup.normalizer (V : Set G), g * x * g⁻¹ = y := by
  classical
  refine exists_conj_mem_normalizer_of_no_fixed V hV ?_ x hx hx1 y hy hy1
  intro w hw hw1 hfix
  have hcardS : Nat.card (S : Subgroup G) = 2 * n := by
    obtain ⟨e⟩ := hiso
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hcardS' : 2 * n = 2 ^ k := by rw [← hcardS, hk]
  have hn_eq : n = 2 ^ (k - 1) := by
    have hk1 : 1 ≤ k := by
      by_contra h'
      have h'1 : k = 0 := by omega
      rw [h'1, pow_zero] at hcardS'
      omega
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ'] at hcardS'
    have h2 : n = 2 ^ k' := Nat.mul_left_cancel (by norm_num) hcardS'
    rw [h2]
    congr 1
  -- conjugate `V` into `S`
  obtain ⟨γ, hγ⟩ := exists_conj_le_sylow_of_fourGroup S n hn hiso hconj V hV
  set W : Subgroup G := (MulAut.conj γ) • V with hWdef
  have hW : Work.GW2.IsFourGroup W := by
    rw [hWdef]; exact isFourGroup_smul (MulAut.conj γ) hV
  have hWS : W ≤ (S : Subgroup G) := by rw [hWdef]; exact hγ
  set w' : G := γ * w * γ⁻¹ with hw'def
  have hw'W : w' ∈ W := by
    rw [hWdef, hw'def]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ (MulAut.conj γ) V).mpr
      ⟨w, hw, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  have hw'1 : w' ≠ 1 := by
    intro h
    exact hw1 (by
      have h1 : w = γ⁻¹ * w' * γ := by rw [hw'def]; group
      rw [h1, h]; group)
  have hbad' : Subgroup.normalizer (W : Set G) ≤ Subgroup.centralizer ({w'} : Set G) := by
    intro nn hn
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    have hnV : γ⁻¹ * nn * γ ∈ Subgroup.normalizer (V : Set G) := by
      rw [hWdef] at hn
      exact mem_normalizer_conj_smul_inv γ V hn
    have h1 := Subgroup.mem_centralizer_iff.mp (hfix hnV) w (Set.mem_singleton w)
    have h2 : w' * nn = nn * w' := by
      have h3 : γ * (w * (γ⁻¹ * nn * γ)) * γ⁻¹ = γ * ((γ⁻¹ * nn * γ) * w) * γ⁻¹ := by
        rw [h1]
      convert h3 using 1 <;> (rw [hw'def]; group)
    exact h2
  rcases Nat.eq_zero_or_pos (k - 1) with hj0 | hj0
  · rw [hn_eq, hj0, pow_zero] at hn
    omega
  · rcases (by omega : k - 1 = 1 ∨ 2 ≤ k - 1) with hk1 | hk3
    · have hn2 : n = 2 := by rw [hn_eq, hk1, pow_one]
      have hcard4 : Nat.card (S : Subgroup G) = 4 := by rw [hcardS, hn2]
      exact bad_false_of_card_four S hcard4 hconj W hW hWS w' hw'W hw'1 hbad'
    · have h4 : 4 ∣ n := by
        rw [hn_eq]
        obtain ⟨j, hj⟩ : ∃ j, k - 1 = j + 2 := ⟨k - 3, by omega⟩
        exact ⟨2 ^ j, by rw [hj, pow_add]; ring⟩
      have hn4 : 4 ≤ n := by
        obtain ⟨c, hc⟩ := h4
        omega
      exact no_bad_config_of_four_le S n hn4 h4 hiso hnoN hconj W hW hWS w' hw'W hw'1 hbad'

end Work.FUS