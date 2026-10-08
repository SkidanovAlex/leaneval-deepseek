import Mathlib
import Submission.Work.FUS.Defs
import Submission.Work.Dihedral.Defs

namespace Work.FUS.DihedralFacts

open DihedralGroup

/-! ## Auxiliary material (private to this file)

The proof of the classification of subgroups of a dihedral group goes through the following
recognition lemma: a group `G` that is the union of a cyclic subgroup `K = ⟨g⟩` and the
coset `K·s`, where `s` is an involution conjugating `g` to `g⁻¹`, is dihedral of order
`2·|K|`.  The isomorphism `DihedralGroup (Nat.card K) ≃* G` sends `r j ↦ g ^ j.val` and
`sr j ↦ s * g ^ j.val`. -/

/-- The candidate isomorphism `DihedralGroup m → G`, `r j ↦ g ^ j.val`, `sr j ↦ s * g ^ j.val`. -/
private def phiFun {G : Type*} [Group G] (g s : G) (m : ℕ) : DihedralGroup m → G
  | DihedralGroup.r j => g ^ ((j.val : ℕ) : ℤ)
  | DihedralGroup.sr j => s * g ^ ((j.val : ℕ) : ℤ)

/-- Powers of `g` agree at exponents congruent modulo `orderOf g`. -/
private lemma zpow_eq_of_cast_eq' {G : Type*} [Group G] {g : G} {m : ℕ} (hm : orderOf g = m)
    {a b : ℤ} (h : (a : ZMod m) = (b : ZMod m)) : g ^ a = g ^ b := by
  have : (a : ZMod (orderOf g)) = (b : ZMod (orderOf g)) := by rw [hm]; exact h
  rw [zpow_eq_zpow_iff_modEq]
  exact (ZMod.intCast_eq_intCast_iff a b (orderOf g)).mp this

/-- `(i + j).val` is congruent to `i.val + j.val` modulo `m`. -/
private lemma zmod_val_add_cast {m : ℕ} [NeZero m] (i j : ZMod m) :
    (((i + j).val : ℤ) : ZMod m) = ((((i.val : ℤ) + (j.val : ℤ) : ℤ)) : ZMod m) := by
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- `(i - j).val` is congruent to `i.val - j.val` modulo `m`. -/
private lemma zmod_val_sub_cast {m : ℕ} [NeZero m] (i j : ZMod m) :
    (((i - j).val : ℤ) : ZMod m) = ((((i.val : ℤ) - (j.val : ℤ) : ℤ)) : ZMod m) := by
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- `phiFun` is multiplicative, provided `orderOf g = m` and `s` is an involution inverting `g`. -/
private lemma phiFun_mul {G : Type*} [Group G] (g s : G) (m : ℕ) [NeZero m] (hm : orderOf g = m)
    (hs2 : s ^ 2 = 1) (hconj : s * g * s⁻¹ = g⁻¹) (a b : DihedralGroup m) :
    phiFun g s m (a * b) = phiFun g s m a * phiFun g s m b := by
  have hs_inv : s⁻¹ = s := by
    have h : s * s = 1 := by rw [← pow_two]; exact hs2
    exact inv_eq_of_mul_eq_one_right h
  have hconj' : ∀ k : ℤ, s * g ^ k * s⁻¹ = g ^ (-k) := by
    intro k
    rw [conj_zpow.symm, hconj, inv_zpow']
  have hsconj : ∀ k : ℤ, s * g ^ k * s = g ^ (-k) := fun k => by simpa [hs_inv] using hconj' k
  have hstep : ∀ k : ℤ, s * g ^ k = g ^ (-k) * s := by
    intro k
    have h := congrArg (fun x => x * s) (hconj' k)
    simpa [mul_assoc] using h
  have hswp : ∀ k : ℤ, g ^ k * s = s * g ^ (-k) := fun k => by simpa using (hstep (-k)).symm
  cases a with
  | r i =>
    cases b with
    | r j =>
      simp only [DihedralGroup.r_mul_r, phiFun]
      rw [← zpow_add]
      exact zpow_eq_of_cast_eq' hm (zmod_val_add_cast i j)
    | sr j =>
      simp only [DihedralGroup.r_mul_sr, phiFun]
      rw [← mul_assoc, hswp, mul_assoc, ← zpow_add]
      rw [show (-(i.val : ℤ) + (j.val : ℤ)) = ((j.val : ℤ) - (i.val : ℤ)) by ring]
      exact congrArg (fun x => s * x) (zpow_eq_of_cast_eq' hm (zmod_val_sub_cast j i))
  | sr i =>
    cases b with
    | r j =>
      simp only [DihedralGroup.sr_mul_r, phiFun]
      rw [mul_assoc, ← zpow_add]
      exact congrArg (fun x => s * x) (zpow_eq_of_cast_eq' hm (zmod_val_add_cast i j))
    | sr j =>
      simp only [DihedralGroup.sr_mul_sr, phiFun]
      rw [← mul_assoc, hsconj, ← zpow_add]
      rw [show (-(i.val : ℤ) + (j.val : ℤ)) = ((j.val : ℤ) - (i.val : ℤ)) by ring]
      exact zpow_eq_of_cast_eq' hm (zmod_val_sub_cast j i)

/-- Recognition lemma: if `K = ⟨g⟩` is a cyclic subgroup of `G`, `s` is an involution outside `K`
acting on `g` by inversion, and `G = K ∪ K·s`, then `G` is dihedral of order `2·Nat.card K`. -/
private theorem recognition_aux (G : Type*) [Group G] [Finite G]
    (K : Subgroup G) (g : K) (hg : Subgroup.zpowers g = ⊤) (s : G) (hs2 : s ^ 2 = 1)
    (hsK : s ∉ K) (hconj : s * (g : G) * s⁻¹ = (g : G)⁻¹)
    (hcover : ∀ x : G, x ∈ K ∨ x * s ∈ K) :
    Nonempty (G ≃* DihedralGroup (Nat.card K)) := by
  haveI : Nonempty K := ⟨1⟩
  have hpos : 0 < Nat.card K := Nat.card_pos
  haveI : NeZero (Nat.card K) := ⟨hpos.ne'⟩
  have hm : orderOf ((g : K) : G) = Nat.card K := by
    rw [Subgroup.orderOf_coe, ← Nat.card_zpowers (g : K), hg]
    exact Nat.card_congr (Subgroup.topEquiv (G := K)).toEquiv
  let φ : DihedralGroup (Nat.card K) →* G :=
    { toFun := phiFun (g : G) s (Nat.card K)
      map_one' := by
        conv_lhs => rw [DihedralGroup.one_def]
        simp [phiFun]
      map_mul' := phiFun_mul (g : G) s (Nat.card K) hm hs2 hconj }
  have hker : ∀ x : DihedralGroup (Nat.card K), φ x = 1 → x = 1 := by
    intro x hx
    cases x with
    | r i =>
      have hxi : (g : G) ^ ((i.val : ℕ) : ℤ) = 1 := hx
      have hdvd : (Nat.card K : ℤ) ∣ ((i.val : ℕ) : ℤ) := by
        have h := orderOf_dvd_iff_zpow_eq_one.mpr hxi
        rwa [hm] at h
      have hdvd' : Nat.card K ∣ i.val := Int.natCast_dvd_natCast.mp hdvd
      have hv : i.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (ZMod.val_lt i)
      rw [show i = 0 from (ZMod.val_eq_zero i).mp hv, DihedralGroup.r_zero]
    | sr i =>
      have hxs : s * (g : G) ^ ((i.val : ℕ) : ℤ) = 1 := hx
      have hmem : ((g : G) ^ ((i.val : ℕ) : ℤ)) ∈ K := Subgroup.zpow_mem K g.2 _
      have hsK' : s ∈ K := by
        have hs_eq : s = ((g : G) ^ ((i.val : ℕ) : ℤ))⁻¹ :=
          eq_inv_of_mul_eq_one_left hxs
        rw [hs_eq]; exact Subgroup.inv_mem K hmem
      exact absurd hsK' hsK
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 : x * y⁻¹ = 1 := by
      refine hker (x * y⁻¹) ?_
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    calc x = x * y⁻¹ * y := by group
      _ = 1 * y := by rw [h1]
      _ = y := by rw [one_mul]
  have hsurj : Function.Surjective φ := by
    have hsrange : s ∈ φ.range := by
      refine ⟨DihedralGroup.sr 0, ?_⟩
      show phiFun (g : G) s (Nat.card K) (DihedralGroup.sr 0) = s
      simp [phiFun]
    have hgrange : (g : G) ∈ φ.range := by
      by_cases hm1 : Nat.card K = 1
      · have hg1 : (g : G) = 1 := by
          have : orderOf (g : G) = 1 := by rw [hm, hm1]
          exact orderOf_eq_one_iff.mp this
        rw [hg1]; exact Subgroup.one_mem _
      · haveI : Fact (1 < Nat.card K) := ⟨by omega⟩
        refine ⟨DihedralGroup.r 1, ?_⟩
        show phiFun (g : G) s (Nat.card K) (DihedralGroup.r 1) = (g : G)
        simp [phiFun, ZMod.val_one]
    have hKle : K ≤ φ.range := by
      intro y hy
      have hy' : (⟨y, hy⟩ : K) ∈ Subgroup.zpowers g := by rw [hg]; exact Subgroup.mem_top _
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hy'
      have hy'' : y = (g : G) ^ a := by
        have h2 := congrArg (fun z : K => (z : G)) ha
        simpa using h2.symm
      rw [hy'']
      exact Subgroup.zpow_mem φ.range hgrange a
    intro y
    rcases hcover y with hy | hy
    · exact hKle hy
    · have hy' : y = (y * s) * s⁻¹ := by group
      rw [hy']
      exact Subgroup.mul_mem φ.range (hKle hy) (Subgroup.inv_mem φ.range hsrange)
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

/-- The rotation part `H ∩ ⟨r⟩` of a subgroup `H ≤ DihedralGroup n`, viewed as a subgroup of `H`,
is cyclic (it embeds into the cyclic group `⟨r⟩`). -/
private theorem isCyclic_comap_rot (n : ℕ) (H : Subgroup (DihedralGroup n)) :
    IsCyclic ((Work.Dihedral.rot n).subgroupOf H) := by
  let f : ↥((Work.Dihedral.rot n).subgroupOf H) →* ↥(Work.Dihedral.rot n) :=
    { toFun := fun x => ⟨(x : ↥H), x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  refine isCyclic_of_injective f (fun a b h => ?_)
  have h1 : ((a : ↥H) : DihedralGroup n) = ((b : ↥H) : DihedralGroup n) :=
    congrArg (fun y : ↥(Work.Dihedral.rot n) => (y : DihedralGroup n)) h
  exact Subtype.ext (Subtype.ext h1)

/-- Every subgroup of a dihedral group is cyclic or dihedral. -/
theorem isCyclic_or_dihedral_of_le_dihedral (n : ℕ) (hn : 2 ≤ n) (H : Subgroup (DihedralGroup n)) :
    IsCyclic H ∨ ∃ m : ℕ, Nonempty (H ≃* DihedralGroup m) := by
  by_cases hle : H ≤ Work.Dihedral.rot n
  · exact Or.inl (isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))
  · right
    obtain ⟨s, hsH, hsR⟩ : ∃ s ∈ H, s ∉ Work.Dihedral.rot n := by
      by_contra h
      exact hle fun x hx => by
        by_contra hx'
        exact h ⟨x, hx, hx'⟩
    obtain ⟨i, rfl⟩ := Work.Dihedral.notMem_rot.mp hsR
    haveI : NeZero n := ⟨by omega⟩
    haveI : Finite ↥H := Subtype.finite
    set K : Subgroup ↥H := (Work.Dihedral.rot n).subgroupOf H with hK
    have hKcyc : IsCyclic K := isCyclic_comap_rot n H
    obtain ⟨g, hg⟩ : ∃ g : K, Subgroup.zpowers g = ⊤ := by
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
      exact ⟨g, le_antisymm le_top fun x _ => hg x⟩
    let S : ↥H := ⟨DihedralGroup.sr i, hsH⟩
    have hS2 : S ^ 2 = 1 := by
      apply Subtype.ext
      simp [S, pow_two]
    have hSK : S ∉ K := by
      intro h
      rw [hK, Subgroup.mem_subgroupOf] at h
      exact hsR h
    have hgrot : ((g : ↥H) : DihedralGroup n) ∈ Work.Dihedral.rot n := g.2
    obtain ⟨a, ha⟩ := Work.Dihedral.mem_rot.mp hgrot
    have hconj_amb : DihedralGroup.sr i * ((g : ↥H) : DihedralGroup n) * DihedralGroup.sr i =
        (((g : ↥H) : DihedralGroup n))⁻¹ := by
      rw [ha, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
      congr 1
      ring
    have hconj : S * (g : ↥H) * S⁻¹ = (g : ↥H)⁻¹ := by
      apply Subtype.ext
      simpa [S, Subgroup.coe_mul, Subgroup.coe_inv] using hconj_amb
    have hcover : ∀ x : ↥H, x ∈ K ∨ x * S ∈ K := by
      intro x
      by_cases hx : (x : DihedralGroup n) ∈ Work.Dihedral.rot n
      · refine Or.inl ?_
        rw [hK]
        exact Subgroup.mem_subgroupOf.mpr hx
      · refine Or.inr ?_
        obtain ⟨j, hj⟩ := Work.Dihedral.notMem_rot.mp hx
        have hxj : ((x * S : ↥H) : DihedralGroup n) = DihedralGroup.r (i - j) := by
          rw [Subgroup.coe_mul, show (x : DihedralGroup n) = DihedralGroup.sr j from hj,
            show (S : DihedralGroup n) = DihedralGroup.sr i from rfl]
          rw [DihedralGroup.sr_mul_sr]
        rw [hK, Subgroup.mem_subgroupOf, hxj]
        exact Work.Dihedral.r_mem_rot _
    obtain ⟨e⟩ := recognition_aux (↥H) K g hg S hS2 hSK hconj hcover
    exact ⟨Nat.card K, ⟨e⟩⟩

end Work.FUS.DihedralFacts
