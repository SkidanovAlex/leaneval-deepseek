import Mathlib

open scoped commutatorElement

namespace Work.DSTR

/-- Auxiliary computation: if `a` commutes with `x` and `y`, `b` commutes with `x` and `y`,
and `a` commutes with `b`, then `⁅a * x, b * y⁆ = ⁅x, y⁆`. -/
lemma commutatorElement_mul_of_commute {G : Type*} [Group G] {a b x y : G}
    (hax : Commute a x) (hay : Commute a y) (hbx : Commute b x) (hby : Commute b y)
    (hab : Commute a b) : ⁅a * x, b * y⁆ = ⁅x, y⁆ := by
  have h2 : ⁅a, b * y⁆ = 1 := (hab.mul_right hay).commutator_eq
  have h4 : ⁅x, b⁆ = 1 := hbx.symm.commutator_eq
  have hcb : Commute b ⁅x, y⁆ := by
    simpa [commutatorElement_def] using
      ((hbx.mul_right hby).mul_right hbx.inv_right).mul_right hby.inv_right
  have hca : Commute a ⁅x, y⁆ := by
    simpa [commutatorElement_def] using
      ((hax.mul_right hay).mul_right hax.inv_right).mul_right hay.inv_right
  have h5 : b * ⁅x, y⁆ * b⁻¹ = ⁅x, y⁆ := by rw [hcb.eq, mul_assoc, mul_inv_cancel, mul_one]
  have h6 : a * ⁅x, y⁆ * a⁻¹ = ⁅x, y⁆ := by rw [hca.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj, h2, h4]
  simp only [one_mul, mul_one]
  rw [h5, h6]

theorem conj_eq_self_of_commutator_mem_center {G : Type*} [Group G] (H : Subgroup G) (hperf : ⁅H, H⁆ = H) (g : G) (h : ∀ s ∈ H, g⁻¹ * s⁻¹ * g * s ∈ (Subgroup.center ↥H).map H.subtype) : ∀ s ∈ H, g * s * g⁻¹ = s := by
  -- `Z` is the center of `H`, viewed as a subgroup of `G`.
  set Z : Subgroup G := (Subgroup.center ↥H).map H.subtype with hZ
  -- Elements of `Z` lie in `H` ...
  have hZmem : ∀ z ∈ Z, z ∈ H := by
    intro z hz
    rw [hZ, Subgroup.mem_map] at hz
    obtain ⟨z', _, rfl⟩ := hz
    exact z'.2
  -- ... and are central in `H`.
  have hZcent : ∀ z ∈ Z, ∀ y ∈ H, z * y = y * z := by
    intro z hz y hy
    rw [hZ, Subgroup.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' ⟨y, hy⟩).symm
  -- The hypothesis, applied to `s⁻¹`, gives `g⁻¹ * s * g * s⁻¹ ∈ Z`.
  have hess : ∀ s ∈ H, g⁻¹ * s * g * s⁻¹ ∈ Z := by
    intro s hs
    simpa using h s⁻¹ (H.inv_mem hs)
  -- Consequently `g` centralizes every commutator of elements of `H`.
  have hcomm : ∀ s ∈ H, ∀ t ∈ H, ⁅s, t⁆ ∈ Subgroup.centralizer ({g} : Set G) := by
    intro s hs t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    set es := g⁻¹ * s * g * s⁻¹ with hes_def
    set et := g⁻¹ * t * g * t⁻¹ with het_def
    have hes : es ∈ Z := by rw [hes_def]; exact hess s hs
    have het : et ∈ Z := by rw [het_def]; exact hess t ht
    have hses : g⁻¹ * s * g = es * s := by rw [hes_def]; group
    have htet : g⁻¹ * t * g = et * t := by rw [het_def]; group
    -- Conjugating the commutator `⁅s, t⁆` by `g`: the central factors cancel.
    have key : g⁻¹ * ⁅s, t⁆ * g = ⁅s, t⁆ := by
      have hconj : g⁻¹ * ⁅s, t⁆ * g = ⁅g⁻¹ * s * g, g⁻¹ * t * g⁆ := by
        simpa using conjugate_commutatorElement s t g⁻¹
      rw [hconj, hses, htet]
      exact commutatorElement_mul_of_commute (a := es) (b := et) (x := s) (y := t)
        (hZcent es hes s hs) (hZcent es hes t ht)
        (hZcent et het s hs) (hZcent et het t ht)
        (hZcent es hes et (hZmem et het))
    calc ⁅s, t⁆ * g = g * (g⁻¹ * ⁅s, t⁆ * g) := by group
      _ = g * ⁅s, t⁆ := by rw [key]
  -- Since `H = ⁅H, H⁆`, we deduce `H ≤ C_G(g)`.
  have hle : H ≤ Subgroup.centralizer ({g} : Set G) :=
    hperf ▸ (Subgroup.commutator_le.mpr hcomm)
  intro s hs
  have hcs : s ∈ Subgroup.centralizer ({g} : Set G) := hle hs
  rw [Subgroup.mem_centralizer_singleton_iff] at hcs
  rw [hcs.symm]; group

end Work.DSTR
