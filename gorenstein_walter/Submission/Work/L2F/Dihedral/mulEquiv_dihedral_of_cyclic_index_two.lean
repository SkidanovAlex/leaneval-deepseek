import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Dihedral

/-- If `w * a * w⁻¹ = a⁻¹`, then `a * w = w * a⁻¹` (in any group). -/
private lemma mul_w_of_conj_inv {G : Type*} [Group G] {w a : G}
    (h : w * a * w⁻¹ = a⁻¹) : a * w = w * a⁻¹ := by
  have h2 : w * a⁻¹ * w⁻¹ = a := by
    rw [show w * a⁻¹ * w⁻¹ = (w * a * w⁻¹)⁻¹ from by group, h, inv_inv]
  have key : w * a⁻¹ = a * w := by
    have := congrArg (· * w) h2
    simpa [mul_assoc] using this
  exact key.symm

/-- A finite group with a cyclic subgroup `C` of index two and an involution `w ∉ C` that inverts
`C` is dihedral of order `2 * |C|`.  Proof: `w ∉ C` of index `2` gives `G = C ∪ wC`, and the map
`DihedralGroup |C| → G`, `r i ↦ g^i`, `sr i ↦ w * g^i` (where `C = ⟨g⟩`) is a well defined bijective
homomorphism, because `w * g^i * w⁻¹ = g^(-i)` and `w² = 1` give exactly the relations
`(r i)(r j) = r (i+j)`, `(r i)(sr j) = sr (j-i)`, `(sr i)(r j) = sr (i+j)`, `(sr i)(sr j) = r (j-i)`
of Mathlib's `DihedralGroup`. -/
theorem mulEquiv_dihedral_of_cyclic_index_two {G : Type*} [Group G] [Finite G] (C : Subgroup G)
    (hcyc : IsCyclic C) (hidx : C.index = 2)
    (h : ∃ w : G, w ∉ C ∧ w * w = 1 ∧ ∀ c ∈ C, w * c * w⁻¹ = c⁻¹) :
    Nonempty (G ≃* DihedralGroup (Nat.card C)) := by
  classical
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top C).1 hcyc
  obtain ⟨w, hwC, hww, hconj⟩ := h
  set n : ℕ := Nat.card C with hn
  have hcard : Nat.card (Subgroup.zpowers g) = n := by rw [hg, hn]
  -- The isomorphism `Multiplicative (ZMod n) ≃* ⟨g⟩`.
  let e : Multiplicative (ZMod n) ≃* Subgroup.zpowers g :=
    zmodMulEquivOfGenerator (G := Subgroup.zpowers g) (g := ⟨g, Subgroup.mem_zpowers g⟩)
      (fun x => by
        rw [Subgroup.mem_zpowers_iff]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
        exact ⟨k, Subtype.ext (by simpa using hk)⟩)
      hcard
  -- `p i = g ^ i`, as an element of `G`.
  let p : ZMod n → G := fun i => (e (Multiplicative.ofAdd i) : G)
  have hp : ∀ i, p i = (e (Multiplicative.ofAdd i) : G) := fun i => rfl
  have hmem : ∀ i, p i ∈ C := by
    intro i
    rw [hp, ← hg]
    exact (e (Multiplicative.ofAdd i)).2
  have pmul : ∀ i j, p (i + j) = p i * p j := by
    intro i j
    rw [hp, hp, hp]
    rw [show (Multiplicative.ofAdd (i + j) : Multiplicative (ZMod n)) =
      Multiplicative.ofAdd i * Multiplicative.ofAdd j from by simp]
    simp
  have pneg : ∀ i, p (-i) = (p i)⁻¹ := by
    intro i
    rw [hp, hp]
    rw [show (Multiplicative.ofAdd (-i) : Multiplicative (ZMod n)) =
      (Multiplicative.ofAdd i)⁻¹ from by simp]
    simp
  have pzero : p 0 = 1 := by rw [hp]; simp
  have pcomm : ∀ i j, p i * p j = p j * p i := by
    intro i j
    rw [← pmul, ← pmul, add_comm]
  have pinj : ∀ i j, p i = p j → i = j := by
    intro i j hij
    rw [hp, hp] at hij
    have h1 : e (Multiplicative.ofAdd i) = e (Multiplicative.ofAdd j) := Subtype.ext hij
    exact e.injective h1
  have hp_mul_w : ∀ i, p i * w = w * (p i)⁻¹ :=
    fun i => mul_w_of_conj_inv (hconj (p i) (hmem i))
  have hp_comm_inv : ∀ i j, (p i)⁻¹ * p j = p j * (p i)⁻¹ := by
    intro i j
    calc (p i)⁻¹ * p j = p (-i) * p j := by rw [pneg]
      _ = p j * p (-i) := pcomm (-i) j
      _ = p j * (p i)⁻¹ := by rw [pneg]
  let φfun : DihedralGroup n → G := fun x => match x with
    | DihedralGroup.r i => p i
    | DihedralGroup.sr i => w * p i
  have phi_r : ∀ i, φfun (DihedralGroup.r i) = p i := fun i => rfl
  have phi_sr : ∀ i, φfun (DihedralGroup.sr i) = w * p i := fun i => rfl
  let φ : DihedralGroup n →* G :=
    { toFun := φfun
      map_one' := by rw [DihedralGroup.one_def, phi_r 0]; exact pzero
      map_mul' := by
        intro a b
        cases a with
        | r i => cases b with
          | r j => rw [DihedralGroup.r_mul_r, phi_r, phi_r, phi_r]; exact pmul i j
          | sr j =>
            rw [DihedralGroup.r_mul_sr, phi_sr, phi_r, phi_sr]
            rw [sub_eq_add_neg, pmul, pneg]
            have key : p i * (w * p j) = (w * p j) * (p i)⁻¹ := by
              calc p i * (w * p j) = (p i * w) * p j := by group
                _ = (w * (p i)⁻¹) * p j := by rw [hp_mul_w i]
                _ = w * ((p i)⁻¹ * p j) := by group
                _ = w * (p j * (p i)⁻¹) := by rw [hp_comm_inv i j]
                _ = (w * p j) * (p i)⁻¹ := by group
            rw [key]; group
        | sr i => cases b with
          | r j => rw [DihedralGroup.sr_mul_r, phi_sr, phi_sr, phi_r]; rw [pmul, mul_assoc]
          | sr j =>
            rw [DihedralGroup.sr_mul_sr, phi_r, phi_sr, phi_sr]
            rw [sub_eq_add_neg, pmul, pneg]
            have key : w * p i * (w * p j) = p j * (p i)⁻¹ := by
              calc w * p i * (w * p j) = (w * (p i * w)) * p j := by group
                _ = (w * (w * (p i)⁻¹)) * p j := by rw [hp_mul_w i]
                _ = (w * w) * ((p i)⁻¹ * p j) := by group
                _ = (p i)⁻¹ * p j := by rw [hww, one_mul]
                _ = p j * (p i)⁻¹ := by rw [hp_comm_inv i j]
            rw [key] }
  have hφ_r : ∀ i, φ (DihedralGroup.r i) = p i := phi_r
  have hφ_sr : ∀ i, φ (DihedralGroup.sr i) = w * p i := phi_sr
  have hsurj : Function.Surjective φ := by
    intro y
    by_cases hy : y ∈ C
    · rw [← hg] at hy
      obtain ⟨i, hi⟩ := e.surjective ⟨y, hy⟩
      refine ⟨DihedralGroup.r (Multiplicative.toAdd i), ?_⟩
      rw [hφ_r, hp]
      rw [show Multiplicative.ofAdd (Multiplicative.toAdd i) = i from by simp]
      exact congrArg Subtype.val hi
    · -- `y ∉ C`, so `w * y ∈ C` by the index-two relation, and `y = w * (w * y)`.
      have hwy : w * y ∈ C := by
        have hiff : (w ∈ C ↔ y ∈ C) := ⟨fun hw => absurd hw hwC, fun hy' => absurd hy' hy⟩
        exact (Subgroup.mul_mem_iff_of_index_two hidx).2 hiff
      rw [← hg] at hwy
      obtain ⟨i, hi⟩ := e.surjective ⟨w * y, hwy⟩
      refine ⟨DihedralGroup.sr (Multiplicative.toAdd i), ?_⟩
      rw [hφ_sr, hp]
      rw [show Multiplicative.ofAdd (Multiplicative.toAdd i) = i from by simp]
      have hie : (e i : G) = w * y := congrArg Subtype.val hi
      rw [hie, ← mul_assoc, hww, one_mul]
  have hinj : Function.Injective φ := by
    intro a b hab
    cases a with
    | r i => cases b with
      | r j =>
        rw [hφ_r, hφ_r] at hab
        exact congrArg DihedralGroup.r (pinj i j hab)
      | sr j =>
        rw [hφ_r, hφ_sr] at hab
        exfalso
        have hw_eq : w = p i * (p j)⁻¹ := by rw [hab]; group
        exact hwC (hw_eq ▸ C.mul_mem (hmem i) (C.inv_mem (hmem j)))
    | sr i => cases b with
      | r j =>
        rw [hφ_sr, hφ_r] at hab
        exfalso
        have hw_eq : w = p j * (p i)⁻¹ := by rw [← hab]; group
        exact hwC (hw_eq ▸ C.mul_mem (hmem j) (C.inv_mem (hmem i)))
      | sr j =>
        rw [hφ_sr, hφ_sr] at hab
        exact congrArg DihedralGroup.sr (pinj i j (mul_left_cancel hab))
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

end Work.L2F.Dihedral
