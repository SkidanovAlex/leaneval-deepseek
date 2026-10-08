import Mathlib
import Submission.Work.Dihedral.Defs

/-!
# Subgroups of a dihedral group are cyclic or dihedral

For `n ≠ 0` we show that every subgroup `H` of `DihedralGroup n` is either cyclic or
isomorphic to `DihedralGroup m` for some `m`.

The proof is the classical one.  Let `rot n = ⟨r⟩ ≤ DihedralGroup n` be the rotation
subgroup, i.e. the kernel of the "sign" homomorphism
`dihedralSign n : DihedralGroup n →* Multiplicative (ZMod 2)`.  Given `H`:

* if `H ≤ rot n` then `H` is a subgroup of a cyclic group, hence cyclic;
* otherwise `H` contains a reflection.  Then `A = H ⊓ rot n` is cyclic, of index `2`
  in `H` (the sign homomorphism restricted to `H` is onto `ZMod 2` with kernel `A`),
  and a reflection `y ∈ H ∖ A` inverts `A` and satisfies `y ^ 2 = 1`.  The general
  lemma `mulEquivDihedralOfCyclicIndexTwo` below then produces `H ≃* DihedralGroup m`.
-/

namespace Work.RED

open DihedralGroup

/-! ## The sign homomorphism -/

/-- `dihedralSign n : DihedralGroup n →* Multiplicative (ZMod 2)` sends rotations to `1`
and reflections to the non-trivial element; its kernel is the rotation subgroup `⟨r⟩`. -/
def dihedralSign (n : ℕ) : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun x := match x with
    | .r _ => 1
    | .sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;> simp
    decide

@[simp] lemma dihedralSign_r (n : ℕ) (i : ZMod n) : dihedralSign n (DihedralGroup.r i) = 1 :=
  rfl

@[simp] lemma dihedralSign_sr (n : ℕ) (i : ZMod n) :
    dihedralSign n (DihedralGroup.sr i) = Multiplicative.ofAdd 1 :=
  rfl

lemma dihedralSign_sr_ne_one (n : ℕ) (i : ZMod n) : dihedralSign n (DihedralGroup.sr i) ≠ 1 := by
  rw [dihedralSign_sr]
  intro h
  exact absurd (congrArg Multiplicative.toAdd h) (by decide)

lemma dihedralSign_eq_one_iff {n : ℕ} {x : DihedralGroup n} :
    dihedralSign n x = 1 ↔ x ∈ Work.Dihedral.rot n := by
  rcases Work.Dihedral.eq_r_or_sr x with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact iff_of_true rfl (Work.Dihedral.r_mem_rot i)
  · exact iff_of_false (dihedralSign_sr_ne_one n i) (Work.Dihedral.sr_notMem_rot i)

lemma dihedralSign_ker (n : ℕ) : (dihedralSign n).ker = Work.Dihedral.rot n := by
  ext x
  rw [MonoidHom.mem_ker, dihedralSign_eq_one_iff]

lemma natCard_multiplicative_zmod_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  simp [Nat.card_eq_fintype_card]

/-! ## Groups with a cyclic subgroup of index two inverted by an involution

Every group `G` with a cyclic subgroup `A` of index two and an element `y ∉ A` of order two
with `y * a * y⁻¹ = a⁻¹` for all `a ∈ A` is `A ⋊ ⟨y⟩` with inversion action, i.e. the
dihedral group of order `2 * Nat.card A`.  The isomorphism is
`r k ↦ (eA (ofAdd k))` and `sr k ↦ (eA (ofAdd (-k))) * y`, where
`eA : Multiplicative (ZMod (Nat.card A)) ≃* A` is any isomorphism from the cyclic group of
order `Nat.card A`. -/

theorem mulEquivDihedralOfCyclicIndexTwo {G : Type*} [Group G] (A : Subgroup G) (y : G)
    (hidx : A.index = 2) (hy : y ∉ A) (hy2 : y ^ 2 = 1)
    (hconj : ∀ a ∈ A, y * a * y⁻¹ = a⁻¹) (hcyc : IsCyclic ↥A) :
    Nonempty (G ≃* DihedralGroup (Nat.card A)) := by
  have hyy : y * y = 1 := by simpa [pow_two] using hy2
  have hconj' : ∀ a ∈ A, y * a = a⁻¹ * y := by
    intro a ha
    have h := hconj a ha
    rw [← h]
    simp [mul_assoc]
  let eA : Multiplicative (ZMod (Nat.card A)) ≃* ↥A := zmodCyclicMulEquiv hcyc
  have hyu : ∀ u : Multiplicative (ZMod (Nat.card A)),
      y * (((eA u : ↥A)) : G) = (((eA u⁻¹ : ↥A)) : G) * y := by
    intro u
    have h := hconj' (((eA u : ↥A)) : G) (eA u).2
    rwa [show (((eA u : ↥A)) : G)⁻¹ = (((eA u⁻¹ : ↥A)) : G) by
          rw [← Subgroup.coe_inv, ← map_inv]] at h
  let F : DihedralGroup (Nat.card A) → G := fun x => match x with
      | DihedralGroup.r k => (eA (Multiplicative.ofAdd k) : ↥A)
      | DihedralGroup.sr k => (eA (Multiplicative.ofAdd (-k)) : ↥A) * y
  have hFmul : ∀ a b, F (a * b) = F a * F b := by
    intro a b
    rcases a with i | i <;> rcases b with j | j
    · show (((eA (Multiplicative.ofAdd (i + j)) : ↥A)) : G)
          = (((eA (Multiplicative.ofAdd i) : ↥A)) : G) * (((eA (Multiplicative.ofAdd j) : ↥A)) : G)
      rw [ofAdd_add, map_mul, Subgroup.coe_mul]
    · show (((eA (Multiplicative.ofAdd (-(j - i))) : ↥A)) : G) * y
          = (((eA (Multiplicative.ofAdd i) : ↥A)) : G) * ((((eA (Multiplicative.ofAdd (-j)) : ↥A)) : G) * y)
      rw [show (Multiplicative.ofAdd (-(j - i)) : Multiplicative (ZMod (Nat.card A)))
            = Multiplicative.ofAdd i * Multiplicative.ofAdd (-j) by
              rw [← ofAdd_add]; congr 1; ring]
      rw [map_mul, Subgroup.coe_mul, mul_assoc]
    · show (((eA (Multiplicative.ofAdd (-(i + j))) : ↥A)) : G) * y
          = ((((eA (Multiplicative.ofAdd (-i)) : ↥A)) : G) * y) * (((eA (Multiplicative.ofAdd j) : ↥A)) : G)
      have h2 : y * (((eA (Multiplicative.ofAdd j) : ↥A)) : G)
          = (((eA (Multiplicative.ofAdd (-j)) : ↥A)) : G) * y := by
        have h := hyu (Multiplicative.ofAdd j)
        rwa [show (Multiplicative.ofAdd j)⁻¹ = Multiplicative.ofAdd (-j) by rw [← ofAdd_neg]] at h
      rw [show (Multiplicative.ofAdd (-(i + j)) : Multiplicative (ZMod (Nat.card A)))
            = Multiplicative.ofAdd (-i) * Multiplicative.ofAdd (-j) by
              rw [← ofAdd_add]; congr 1; ring]
      rw [map_mul, Subgroup.coe_mul]
      calc ((((eA (Multiplicative.ofAdd (-i)) : ↥A)) : G) * (((eA (Multiplicative.ofAdd (-j)) : ↥A)) : G)) * y
          = (((eA (Multiplicative.ofAdd (-i)) : ↥A)) : G) * ((((eA (Multiplicative.ofAdd (-j)) : ↥A)) : G) * y) := mul_assoc _ _ _
        _ = (((eA (Multiplicative.ofAdd (-i)) : ↥A)) : G) * (y * (((eA (Multiplicative.ofAdd j) : ↥A)) : G)) := by rw [h2]
        _ = ((((eA (Multiplicative.ofAdd (-i)) : ↥A)) : G) * y) * (((eA (Multiplicative.ofAdd j) : ↥A)) : G) := (mul_assoc _ _ _).symm
    · show (((eA (Multiplicative.ofAdd (j - i)) : ↥A)) : G)
          = ((((eA (Multiplicative.ofAdd (-i)) : ↥A)) : G) * y) * ((((eA (Multiplicative.ofAdd (-j)) : ↥A)) : G) * y)
      have h2 : y * (((eA (Multiplicative.ofAdd (-j)) : ↥A)) : G)
          = (((eA (Multiplicative.ofAdd j) : ↥A)) : G) * y := by
        have h := hyu (Multiplicative.ofAdd (-j))
        rwa [show (Multiplicative.ofAdd (-j))⁻¹ = Multiplicative.ofAdd j by
          rw [← ofAdd_neg, neg_neg]] at h
      rw [show (Multiplicative.ofAdd (j - i) : Multiplicative (ZMod (Nat.card A)))
            = Multiplicative.ofAdd (-i) * Multiplicative.ofAdd j by
              rw [← ofAdd_add]; congr 1; ring]
      rw [map_mul, Subgroup.coe_mul]
      rw [mul_assoc, ← mul_assoc y _ y, h2, mul_assoc, hyy, mul_one]
  let ψ : DihedralGroup (Nat.card A) →* G := MonoidHom.mk' F hFmul
  have hψ : ∀ x, ψ x = F x := fun x => rfl
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff ψ, Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : F x = 1 := by rw [← hψ]; exact hx
    rcases x with k | k
    · have h : (((eA (Multiplicative.ofAdd k) : ↥A)) : G) = 1 := by simpa only [F] using hx'
      have h2 : eA (Multiplicative.ofAdd k) = 1 := by apply Subtype.ext; simpa using h
      have h3 : Multiplicative.ofAdd k = 1 := eA.injective (by simpa using h2)
      have h4 : k = 0 := Multiplicative.ofAdd.injective (by simpa using h3)
      rw [h4]; rfl
    · exfalso
      have h : (((eA (Multiplicative.ofAdd (-k)) : ↥A)) : G) * y = 1 := by simpa only [F] using hx'
      have hyA : y ∈ A := by
        have hy_eq : y = (((eA (Multiplicative.ofAdd (-k)) : ↥A)) : G)⁻¹ :=
          eq_inv_of_mul_eq_one_right h
        rw [hy_eq]
        exact A.inv_mem (eA (Multiplicative.ofAdd (-k))).2
      exact hy hyA
  have hsurj : Function.Surjective ψ := by
    have hAle : A ≤ ψ.range := by
      intro a ha
      obtain ⟨k, hk⟩ : ∃ k : ZMod (Nat.card A), (((eA (Multiplicative.ofAdd k) : ↥A)) : G) = a := by
        obtain ⟨u, hu⟩ := eA.surjective ⟨a, ha⟩
        exact ⟨u.toAdd, by rw [ofAdd_toAdd]; simpa using congrArg Subtype.val hu⟩
      exact ⟨DihedralGroup.r k, by rw [hψ]; exact hk⟩
    have hyIn : y ∈ ψ.range := by
      refine ⟨DihedralGroup.sr 0, ?_⟩
      rw [hψ]
      show (((eA (Multiplicative.ofAdd (-(0 : ZMod (Nat.card A)))) : ↥A)) : G) * y = y
      simp
    have hsup : A ⊔ Subgroup.zpowers y = ⊤ := by
      have hrel : A.relIndex (A ⊔ Subgroup.zpowers y) * (A ⊔ Subgroup.zpowers y).index = 2 := by
        rw [Subgroup.relIndex_mul_index le_sup_left, hidx]
      have hdiv : (A ⊔ Subgroup.zpowers y).index ∣ 2 :=
        ⟨A.relIndex (A ⊔ Subgroup.zpowers y), by rw [mul_comm, ← hrel]⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
      · exact Subgroup.index_eq_one.mp h1
      · exfalso
        have hrel1 : A.relIndex (A ⊔ Subgroup.zpowers y) = 1 := by
          rw [h2] at hrel
          exact Nat.mul_right_cancel (by norm_num) hrel
        have : (A ⊔ Subgroup.zpowers y) ≤ A := Subgroup.relIndex_eq_one.mp hrel1
        exact hy (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
    intro x
    have hle : A ⊔ Subgroup.zpowers y ≤ ψ.range := sup_le hAle (Subgroup.zpowers_le.mpr hyIn)
    rw [hsup] at hle
    have hx : x ∈ ψ.range := hle trivial
    exact MonoidHom.mem_range.mp hx
  exact ⟨(MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm⟩

/-! ## The main theorem -/

theorem DihedralSubgroup (n : ℕ) [NeZero n] (H : Subgroup (DihedralGroup n)) :
    IsCyclic ↥H ∨ ∃ m : ℕ, Nonempty (↥H ≃* DihedralGroup m) := by
  by_cases hH : H ≤ Work.Dihedral.rot n
  · exact Or.inl (Subgroup.isCyclic_of_le hH)
  · right
    -- `H` contains an element outside the rotation subgroup, i.e. a reflection.
    have hH' : ∃ g ∈ H, g ∉ Work.Dihedral.rot n := by
      by_contra h
      apply hH
      intro x hx
      by_contra hxR
      exact h ⟨x, hx, hxR⟩
    obtain ⟨g, hgH, hgR⟩ := hH'
    obtain ⟨i, hi⟩ := Work.Dihedral.notMem_rot.mp hgR
    -- The rotation part `A = H ⊓ rot n`, viewed inside `↥H`, and a reflection `y ∈ H`.
    let A : Subgroup ↥H := (H ⊓ Work.Dihedral.rot n).subgroupOf H
    let y : ↥H := ⟨g, hgH⟩
    refine ⟨Nat.card A, ?_⟩
    have hy : y ∉ A := by
      intro hcon
      have h1 : g ∈ Work.Dihedral.rot n := (Subgroup.mem_subgroupOf.mp hcon).2
      rw [hi] at h1
      exact Work.Dihedral.sr_notMem_rot i h1
    have hy2 : y ^ 2 = 1 := by
      apply Subtype.ext
      push_cast
      change g ^ 2 = 1
      rw [hi, sq, DihedralGroup.sr_mul_self]
    have hconj : ∀ a ∈ A, y * a * y⁻¹ = a⁻¹ := by
      intro a ha
      have haR : (a : DihedralGroup n) ∈ Work.Dihedral.rot n :=
        (Subgroup.mem_subgroupOf.mp ha).2
      obtain ⟨k, hk⟩ := Work.Dihedral.mem_rot.mp haR
      apply Subtype.ext
      push_cast
      change g * (a : DihedralGroup n) * g⁻¹ = (a : DihedralGroup n)⁻¹
      rw [hi, hk, DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
        DihedralGroup.inv_r]
      congr 1
      ring
    have hcyc : IsCyclic ↥A := by
      have h1 : IsCyclic ↥(H ⊓ Work.Dihedral.rot n) := Subgroup.isCyclic_of_le inf_le_right
      exact (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ Work.Dihedral.rot n ≤ H)).isCyclic.mpr
        h1
    -- `A` has index two, because the restriction of the sign map to `H` is onto `ZMod 2`
    -- and has kernel `A`.
    have hidx : A.index = 2 := by
      let f : ↥H →* Multiplicative (ZMod 2) := (dihedralSign n).comp H.subtype
      have hfker : f.ker = A := by
        ext x
        rw [MonoidHom.mem_ker, show f x = dihedralSign n (x : DihedralGroup n) from rfl,
          dihedralSign_eq_one_iff, Subgroup.mem_subgroupOf]
        exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
      have hfrange : f.range = ⊤ := by
        have hne : f ⟨g, hgH⟩ ≠ 1 := by
          change dihedralSign n (g : DihedralGroup n) ≠ 1
          rw [show g = DihedralGroup.sr i from hi]
          exact dihedralSign_sr_ne_one n i
        haveI : Fact (Nat.card (Multiplicative (ZMod 2))).Prime :=
          ⟨by rw [natCard_multiplicative_zmod_two]; norm_num⟩
        rcases Subgroup.eq_bot_or_eq_top_of_prime_card f.range with h | h
        · exfalso
          have hmem : f ⟨g, hgH⟩ ∈ f.range := ⟨⟨g, hgH⟩, rfl⟩
          rw [h, Subgroup.mem_bot] at hmem
          exact hne hmem
        · exact h
      rw [← hfker, Subgroup.index_ker, hfrange, Subgroup.card_top,
        natCard_multiplicative_zmod_two]
    exact mulEquivDihedralOfCyclicIndexTwo A y hidx hy hy2 hconj hcyc

end Work.RED
