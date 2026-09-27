import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.HeisMul
import Submission.Work.EKLContract.Lemmas.isHoro_sup_same_source
import Submission.Work.EKLContract.Lemmas.isHoro_sup_same_target

/-!
# C7: the Heisenberg factor

The root groups `U_ij`, `U_jk`, `U_ik` of a triple `i, j, k` of distinct indices of `Fin 3`
generate the Heisenberg group `Heis3 = U_ij ⊔ U_jk ⊔ U_ik`, whose centre is `U_ik`, and the
parametrisation `heis p q r = u_ij(p) · u_jk(r) · u_ik(q - p r)` is a bijection `ℝ³ → Heis3`.
This file records that bijection together with the group-theoretic structure of the two
abelian complements `VjkIk = U_jk ⊔ U_ik`, `VijIk = U_ij ⊔ U_ik`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC7

open Work.EKLContract
open Work.EKLContract.Lemmas

/-! ## Elementary `heis` API -/

/-- Congruence for `heis` in its three real parameters. -/
theorem heis_congr {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {p q r p' q' r' : ℝ} (hp : p = p') (hq : q = q') (hr : r = r') :
    heis hij hjk hik p q r = heis hij hjk hik p' q' r' := by
  rw [hp, hq, hr]

/-! ## The image of `heis` is a subgroup

The multiplication and inversion laws `heis_mul`, `heis_inv` exhibited in `HeisMul.lean` show
that the range of `(p,q,r) ↦ heis p q r` is closed under multiplication and inversion; since
it contains each of the three root groups, it is exactly `Heis3`. -/

/-- The image of the Heisenberg parametrisation, as a subgroup of `SL₃(ℝ)`. -/
def HeisRange {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) : Subgroup SL3 where
  carrier := Set.range (fun x : ℝ × ℝ × ℝ => heis hij hjk hik x.1 x.2.1 x.2.2)
  one_mem' := ⟨(0, 0, 0), heis_zero hij hjk hik⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨(x.1 + y.1, x.2.1 + y.2.1 + x.1 * y.2.2, x.2.2 + y.2.2),
      (heis_mul hij hjk hik x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2).symm⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(-x.1, x.1 * x.2.2 - x.2.1, -x.2.2),
      (heis_inv hij hjk hik x.1 x.2.1 x.2.2).symm⟩

theorem mem_HeisRange_iff {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (g : SL3) : g ∈ HeisRange hij hjk hik ↔ ∃ p q r : ℝ, heis hij hjk hik p q r = g := by
  constructor
  · rintro ⟨⟨p, q, r⟩, h⟩; exact ⟨p, q, r, h⟩
  · rintro ⟨p, q, r, h⟩; exact ⟨(p, q, r), h⟩

theorem Heis3_le_HeisRange {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Heis3 hij hjk hik ≤ HeisRange hij hjk hik := by
  show Uij hij ⊔ Uij hjk ⊔ Uij hik ≤ HeisRange hij hjk hik
  refine sup_le (sup_le ?_ ?_) ?_
  · intro g hg
    obtain ⟨s, rfl⟩ := (horoUij_mem_iff hij g).mp hg
    exact ⟨(s, 0, 0), heis_uij hij hjk hik s⟩
  · intro g hg
    obtain ⟨s, rfl⟩ := (horoUij_mem_iff hjk g).mp hg
    exact ⟨(0, 0, s), heis_ujk hij hjk hik s⟩
  · intro g hg
    obtain ⟨s, rfl⟩ := (horoUij_mem_iff hik g).mp hg
    exact ⟨(0, s, 0), heis_uik hij hjk hik s⟩

theorem HeisRange_le_Heis3 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    HeisRange hij hjk hik ≤ Heis3 hij hjk hik := by
  intro g hg
  obtain ⟨p, q, r, rfl⟩ := (mem_HeisRange_iff hij hjk hik g).mp hg
  exact heis_mem hij hjk hik p q r

/-- **The parametrisation is a bijection `ℝ³ → Heis3`.** -/
theorem mem_Heis3_iff {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (g : SL3) :
    g ∈ Heis3 hij hjk hik ↔ ∃ p q r : ℝ, heis hij hjk hik p q r = g :=
  ⟨fun hg => (mem_HeisRange_iff hij hjk hik g).mp (Heis3_le_HeisRange hij hjk hik hg),
   fun ⟨p, q, r, h⟩ => h ▸ heis_mem hij hjk hik p q r⟩

/-! ## Matrix entries of the transvections -/

theorem uij_eval_self {i j : Fin 3} (h : i ≠ j) (s : ℝ) : toMat (uij h s) i j = s := by
  rw [horoUij_toMat h, Matrix.add_apply, Matrix.one_apply_ne h, Matrix.single_apply,
    if_pos ⟨rfl, rfl⟩, zero_add]

theorem uij_eval_off {i j : Fin 3} (h : i ≠ j) (s : ℝ) {a b : Fin 3}
    (hab : ¬(a = i ∧ b = j)) : toMat (uij h s) a b = (1 : Matrix (Fin 3) (Fin 3) ℝ) a b :=
  horoUij_apply_ne h s (fun hh => hab ⟨hh.1.symm, hh.2.symm⟩)

/-! ## The two abelian complements -/

/-- `heis 0 q r ∈ VjkIk = U_jk ⊔ U_ik`. -/
theorem heis_0qr_mem {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (q r : ℝ) :
    heis hij hjk hik 0 q r ∈ VjkIk hjk hik := by
  have heq : heis hij hjk hik 0 q r = uij hjk r * uij hik q := by
    rw [heis, horoUij_zero hij]
    simp only [one_mul, zero_mul, mul_zero, sub_zero]
  rw [heq]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨r, rfl⟩))
    (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨q, rfl⟩))

/-- `heis p q 0 ∈ VijIk = U_ij ⊔ U_ik`. -/
theorem heis_pq0_mem {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p q : ℝ) :
    heis hij hjk hik p q 0 ∈ VijIk hij hik := by
  have heq : heis hij hjk hik p q 0 = uij hij p * uij hik q := by
    rw [heis, horoUij_zero hjk]
    simp only [mul_one, zero_mul, mul_zero, sub_zero]
  rw [heq]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨p, rfl⟩))
    (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨q, rfl⟩))

/-! ## Conjugation formulae

All four conjugacy relations are immediate from the Heisenberg multiplication law
(`u_ij(p)·u_jk(r)` picks up the central correction `u_ik(p r)`). -/

theorem conj_uij_ujk {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p r : ℝ) :
    uij hij p * uij hjk r * (uij hij p)⁻¹ = heis hij hjk hik 0 (p * r) r := by
  have h1 : uij hij p * uij hjk r * (uij hij p)⁻¹
      = heis hij hjk hik p 0 0 * heis hij hjk hik 0 0 r * (heis hij hjk hik p 0 0)⁻¹ := by
    rw [← heis_uij hij hjk hik p, ← heis_ujk hij hjk hik r]
  have h2 : heis hij hjk hik p 0 0 * heis hij hjk hik 0 0 r * (heis hij hjk hik p 0 0)⁻¹
      = heis hij hjk hik p 0 0 * heis hij hjk hik 0 0 r * heis hij hjk hik (-p) 0 0 := by
    rw [heis_inv hij hjk hik p 0 0,
      show heis hij hjk hik (-p) (p * 0 - 0) (-0) = heis hij hjk hik (-p) 0 0 from
        heis_congr hij hjk hik (by ring) (by ring) (by ring)]
  have h3 : heis hij hjk hik p 0 0 * heis hij hjk hik 0 0 r * heis hij hjk hik (-p) 0 0
      = heis hij hjk hik 0 (p * r) r := by
    rw [heis_mul, heis_mul]
    exact heis_congr hij hjk hik (by ring) (by ring) (by ring)
  rw [h1, h2, h3]

theorem conj_uij_uik {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p q : ℝ) :
    uij hij p * uij hik q * (uij hij p)⁻¹ = heis hij hjk hik 0 q 0 := by
  have h1 : uij hij p * uij hik q * (uij hij p)⁻¹
      = heis hij hjk hik p 0 0 * heis hij hjk hik 0 q 0 * (heis hij hjk hik p 0 0)⁻¹ := by
    rw [← heis_uij hij hjk hik p, ← heis_uik hij hjk hik q]
  have h2 : heis hij hjk hik p 0 0 * heis hij hjk hik 0 q 0 * (heis hij hjk hik p 0 0)⁻¹
      = heis hij hjk hik p 0 0 * heis hij hjk hik 0 q 0 * heis hij hjk hik (-p) 0 0 := by
    rw [heis_inv hij hjk hik p 0 0,
      show heis hij hjk hik (-p) (p * 0 - 0) (-0) = heis hij hjk hik (-p) 0 0 from
        heis_congr hij hjk hik (by ring) (by ring) (by ring)]
  have h3 : heis hij hjk hik p 0 0 * heis hij hjk hik 0 q 0 * heis hij hjk hik (-p) 0 0
      = heis hij hjk hik 0 q 0 := by
    rw [heis_mul, heis_mul]
    exact heis_congr hij hjk hik (by ring) (by ring) (by ring)
  rw [h1, h2, h3]

theorem conj_ujk_uij {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (r s : ℝ) :
    uij hjk r * uij hij s * (uij hjk r)⁻¹ = heis hij hjk hik s (-(s * r)) 0 := by
  have h1 : uij hjk r * uij hij s * (uij hjk r)⁻¹
      = heis hij hjk hik 0 0 r * heis hij hjk hik s 0 0 * (heis hij hjk hik 0 0 r)⁻¹ := by
    rw [← heis_ujk hij hjk hik r, ← heis_uij hij hjk hik s]
  have h2 : heis hij hjk hik 0 0 r * heis hij hjk hik s 0 0 * (heis hij hjk hik 0 0 r)⁻¹
      = heis hij hjk hik 0 0 r * heis hij hjk hik s 0 0 * heis hij hjk hik 0 0 (-r) := by
    rw [heis_inv hij hjk hik 0 0 r,
      show heis hij hjk hik (-0) (0 * r - 0) (-r) = heis hij hjk hik 0 0 (-r) from
        heis_congr hij hjk hik (by ring) (by ring) (by ring)]
  have h3 : heis hij hjk hik 0 0 r * heis hij hjk hik s 0 0 * heis hij hjk hik 0 0 (-r)
      = heis hij hjk hik s (-(s * r)) 0 := by
    rw [heis_mul, heis_mul]
    exact heis_congr hij hjk hik (by ring) (by ring) (by ring)
  rw [h1, h2, h3]

theorem conj_ujk_uik {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (r t : ℝ) :
    uij hjk r * uij hik t * (uij hjk r)⁻¹ = heis hij hjk hik 0 t 0 := by
  have h1 : uij hjk r * uij hik t * (uij hjk r)⁻¹
      = heis hij hjk hik 0 0 r * heis hij hjk hik 0 t 0 * (heis hij hjk hik 0 0 r)⁻¹ := by
    rw [← heis_ujk hij hjk hik r, ← heis_uik hij hjk hik t]
  have h2 : heis hij hjk hik 0 0 r * heis hij hjk hik 0 t 0 * (heis hij hjk hik 0 0 r)⁻¹
      = heis hij hjk hik 0 0 r * heis hij hjk hik 0 t 0 * heis hij hjk hik 0 0 (-r) := by
    rw [heis_inv hij hjk hik 0 0 r,
      show heis hij hjk hik (-0) (0 * r - 0) (-r) = heis hij hjk hik 0 0 (-r) from
        heis_congr hij hjk hik (by ring) (by ring) (by ring)]
  have h3 : heis hij hjk hik 0 0 r * heis hij hjk hik 0 t 0 * heis hij hjk hik 0 0 (-r)
      = heis hij hjk hik 0 t 0 := by
    rw [heis_mul, heis_mul]
    exact heis_congr hij hjk hik (by ring) (by ring) (by ring)
  rw [h1, h2, h3]

/-! ## Centrallity of `U_ik` -/

theorem centre_Uik {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ g ∈ Uij hik, ∀ h ∈ Heis3 hij hjk hik, h * g = g * h := by
  intro g hg h hh
  obtain ⟨s, rfl⟩ := (horoUij_mem_iff hik g).mp hg
  obtain ⟨p, q, r, rfl⟩ := (mem_Heis3_iff hij hjk hik h).mp hh
  rw [← heis_uik hij hjk hik s, heis_mul, heis_mul]
  exact heis_congr hij hjk hik (by ring) (by ring) (by ring)

/-! ## The two decompositions of `Heis3` -/

theorem split_VjkIk {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ h ∈ Heis3 hij hjk hik, ∃ g ∈ Uij hij, ∃ u ∈ VjkIk hjk hik, h = g * u := by
  intro h hh
  obtain ⟨p, q, r, rfl⟩ := (mem_Heis3_iff hij hjk hik h).mp hh
  refine ⟨uij hij p, Subgroup.subset_closure ⟨p, rfl⟩,
    uij hjk r * uij hik (q - p * r), ?_, ?_⟩
  · exact mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨r, rfl⟩))
      (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨q - p * r, rfl⟩))
  · unfold heis
    rw [mul_assoc]

theorem split_VijIk {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ h ∈ Heis3 hij hjk hik, ∃ g ∈ Uij hjk, ∃ u ∈ VijIk hij hik, h = g * u := by
  intro h hh
  obtain ⟨p, q, r, rfl⟩ := (mem_Heis3_iff hij hjk hik h).mp hh
  refine ⟨uij hjk r, Subgroup.subset_closure ⟨r, rfl⟩,
    (uij hjk r)⁻¹ * heis hij hjk hik p q r, ?_, ?_⟩
  · have h1 : (uij hjk r)⁻¹ = heis hij hjk hik 0 0 (-r) := by
      rw [← heis_ujk hij hjk hik r, heis_inv hij hjk hik 0 0 r]
      exact heis_congr hij hjk hik (by ring) (by ring) (by ring)
    rw [h1, heis_mul,
      show heis hij hjk hik (0 + p) (0 + q + 0 * r) (-r + r) = heis hij hjk hik p q 0 from
        heis_congr hij hjk hik (by ring) (by ring) (by ring)]
    exact heis_pq0_mem hij hjk hik p q
  · exact (mul_inv_cancel_left (uij hjk r) (heis hij hjk hik p q r)).symm

theorem split_VjkIk_2 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ h ∈ VjkIk hjk hik, ∃ g ∈ Uij hjk, ∃ u ∈ Uij hik, h = g * u := by
  intro h hh
  rw [VjkIk] at hh
  obtain ⟨s, t, hst⟩ := (mem_sup_Uij_same_target_prod hjk hik hij.symm h).mp hh
  exact ⟨uij hjk s, Subgroup.subset_closure ⟨s, rfl⟩, uij hik t,
    Subgroup.subset_closure ⟨t, rfl⟩, hst.symm⟩

theorem split_VijIk_2 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ h ∈ VijIk hij hik, ∃ g ∈ Uij hij, ∃ u ∈ Uij hik, h = g * u := by
  intro h hh
  rw [VijIk, srcU_sup_eq_sub hij hik] at hh
  obtain ⟨s, t, hst⟩ := (srcU_mem_sub hij hik h).mp hh
  refine ⟨uij hij s, Subgroup.subset_closure ⟨s, rfl⟩, uij hik t,
    Subgroup.subset_closure ⟨t, rfl⟩, ?_⟩
  show h = uij hij s * uij hik t
  rw [← hst]
  rfl

/-! ## Normalisation -/

theorem normalize_14 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ g ∈ Uij hij, ∀ u ∈ VjkIk hjk hik, g * u * g⁻¹ ∈ VjkIk hjk hik := by
  intro g hg u hu
  obtain ⟨p, rfl⟩ := (horoUij_mem_iff hij g).mp hg
  rw [VjkIk] at hu
  obtain ⟨s, t, rfl⟩ := (mem_sup_Uij_same_target_prod hjk hik hij.symm u).mp hu
  have key : uij hij p * (uij hjk s * uij hik t) * (uij hij p)⁻¹
      = (uij hij p * uij hjk s * (uij hij p)⁻¹)
        * (uij hij p * uij hik t * (uij hij p)⁻¹) := by group
  rw [key, conj_uij_ujk hij hjk hik p s, conj_uij_uik hij hjk hik p t]
  exact mul_mem (heis_0qr_mem hij hjk hik (p * s) s) (heis_0qr_mem hij hjk hik t 0)

theorem normalize_15 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ g ∈ Uij hjk, ∀ u ∈ VijIk hij hik, g * u * g⁻¹ ∈ VijIk hij hik := by
  intro g hg u hu
  obtain ⟨r, rfl⟩ := (horoUij_mem_iff hjk g).mp hg
  rw [VijIk, srcU_sup_eq_sub hij hik] at hu
  obtain ⟨s, t, hst⟩ := (srcU_mem_sub hij hik u).mp hu
  rw [← hst]
  change uij hjk r * (uij hij s * uij hik t) * (uij hjk r)⁻¹ ∈ VijIk hij hik
  have key : uij hjk r * (uij hij s * uij hik t) * (uij hjk r)⁻¹
      = (uij hjk r * uij hij s * (uij hjk r)⁻¹)
        * (uij hjk r * uij hik t * (uij hjk r)⁻¹) := by group
  rw [key, conj_ujk_uij hij hjk hik r s, conj_ujk_uik hij hjk hik r t]
  exact mul_mem (heis_pq0_mem hij hjk hik s (-(s * r))) (heis_pq0_mem hij hjk hik 0 t)

theorem normalize_16 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ g ∈ Uij hjk, ∀ u ∈ Uij hik, g * u * g⁻¹ ∈ Uij hik := by
  intro g hg u hu
  obtain ⟨r, rfl⟩ := (horoUij_mem_iff hjk g).mp hg
  obtain ⟨t, rfl⟩ := (horoUij_mem_iff hik u).mp hu
  rw [conj_ujk_uik hij hjk hik r t, heis_uik hij hjk hik t]
  exact Subgroup.subset_closure ⟨t, rfl⟩

theorem normalize_17 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ g ∈ Uij hij, ∀ u ∈ Uij hik, g * u * g⁻¹ ∈ Uij hik := by
  intro g hg u hu
  obtain ⟨p, rfl⟩ := (horoUij_mem_iff hij g).mp hg
  obtain ⟨q, rfl⟩ := (horoUij_mem_iff hik u).mp hu
  rw [conj_uij_uik hij hjk hik p q, heis_uik hij hjk hik q]
  exact Subgroup.subset_closure ⟨q, rfl⟩

/-! ## Trivial intersections -/

theorem VjkIk_entry_ij {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {g : SL3} (hg : g ∈ VjkIk hjk hik) : toMat g i j = 0 := by
  rw [VjkIk] at hg
  have h := (st_mem_sup_iff_entries hjk hik hij.symm g).mp hg
  have hcond : ¬((i = j ∧ j = k) ∨ (i = i ∧ j = k)) := by
    rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact hij h1
    · exact hjk h2
  rw [h i j hcond, Matrix.one_apply_ne hij]

theorem VijIk_entry_jk {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {g : SL3} (hg : g ∈ VijIk hij hik) : toMat g j k = 0 := by
  rw [VijIk, srcU_sup_eq_sub hij hik] at hg
  obtain ⟨s, t, rfl⟩ := (srcU_mem_sub hij hik g).mp hg
  rw [srcU_toMat]
  have h1 : (Matrix.single i j s : Matrix (Fin 3) (Fin 3) ℝ) j k = 0 := by
    rw [Matrix.single_apply]; exact if_neg (fun h => hij h.1)
  have h2 : (Matrix.single i k t : Matrix (Fin 3) (Fin 3) ℝ) j k = 0 := by
    rw [Matrix.single_apply]; exact if_neg (fun h => hij h.1)
  rw [Matrix.add_apply, Matrix.add_apply, h1, h2, Matrix.one_apply_ne hjk]
  simp

theorem disjoint_Uij_VjkIk {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ g : SL3, g ∈ Uij hij → g ∈ VjkIk hjk hik → g = 1 := by
  intro g hg1 hg2
  obtain ⟨p, rfl⟩ := (horoUij_mem_iff hij g).mp hg1
  have h0 : toMat (uij hij p) i j = 0 := VjkIk_entry_ij hij hjk hik hg2
  rw [uij_eval_self hij p] at h0
  rw [h0]
  exact horoUij_zero hij

theorem disjoint_Ujk_VijIk {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ g : SL3, g ∈ Uij hjk → g ∈ VijIk hij hik → g = 1 := by
  intro g hg1 hg2
  obtain ⟨p, rfl⟩ := (horoUij_mem_iff hjk g).mp hg1
  have h0 : toMat (uij hjk p) j k = 0 := VijIk_entry_jk hij hjk hik hg2
  rw [uij_eval_self hjk p] at h0
  rw [h0]
  exact horoUij_zero hjk

theorem disjoint_Ujk_Uik {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ g : SL3, g ∈ Uij hjk → g ∈ Uij hik → g = 1 := by
  intro g hg1 hg2
  obtain ⟨p, hgp⟩ := (horoUij_mem_iff hjk g).mp hg1
  obtain ⟨q, hgq⟩ := (horoUij_mem_iff hik g).mp hg2
  have h1 : toMat g j k = p := by rw [← hgp]; exact uij_eval_self hjk p
  have h2 : toMat g j k = 0 := by
    rw [← hgq, uij_eval_off hik q (by rintro ⟨h1', _⟩; exact hij.symm h1'),
      Matrix.one_apply_ne hjk]
  rw [h1] at h2
  rw [← hgp, h2]
  exact horoUij_zero hjk

theorem disjoint_Uij_Uik {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ g : SL3, g ∈ Uij hij → g ∈ Uij hik → g = 1 := by
  intro g hg1 hg2
  obtain ⟨p, hgp⟩ := (horoUij_mem_iff hij g).mp hg1
  obtain ⟨q, hgq⟩ := (horoUij_mem_iff hik g).mp hg2
  have h1 : toMat g i j = p := by rw [← hgp]; exact uij_eval_self hij p
  have h2 : toMat g i j = 0 := by
    rw [← hgq, uij_eval_off hik q (by rintro ⟨_, h2'⟩; exact hjk h2'),
      Matrix.one_apply_ne hij]
  rw [h1] at h2
  rw [← hgp, h2]
  exact horoUij_zero hij

/-! ## The main statement -/

theorem HeisFactor : ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
    (∀ g : Work.EKLContract.SL3, g ∈ Work.EKLC7.Heis3 hij hjk hik ↔
        ∃ p q r : ℝ, Work.EKLC7.heis hij hjk hik p q r = g)
    ∧ (Work.EKLContract.Uij hij ≤ Work.EKLC7.Heis3 hij hjk hik)
    ∧ (Work.EKLContract.Uij hjk ≤ Work.EKLC7.Heis3 hij hjk hik)
    ∧ (Work.EKLContract.Uij hik ≤ Work.EKLC7.Heis3 hij hjk hik)
    ∧ (Work.EKLContract.Uij hjk ≤ Work.EKLC7.VjkIk hjk hik)
    ∧ (Work.EKLContract.Uij hik ≤ Work.EKLC7.VjkIk hjk hik)
    ∧ (Work.EKLContract.Uij hij ≤ Work.EKLC7.VijIk hij hik)
    ∧ (Work.EKLContract.Uij hik ≤ Work.EKLC7.VijIk hij hik)
    ∧ (∀ g ∈ Work.EKLContract.Uij hik, ∀ h ∈ Work.EKLC7.Heis3 hij hjk hik, h * g = g * h)
    ∧ (∀ h ∈ Work.EKLC7.Heis3 hij hjk hik, ∃ g ∈ Work.EKLContract.Uij hij,
        ∃ u ∈ Work.EKLC7.VjkIk hjk hik, h = g * u)
    ∧ (∀ h ∈ Work.EKLC7.Heis3 hij hjk hik, ∃ g ∈ Work.EKLContract.Uij hjk,
        ∃ u ∈ Work.EKLC7.VijIk hij hik, h = g * u)
    ∧ (∀ h ∈ Work.EKLC7.VjkIk hjk hik, ∃ g ∈ Work.EKLContract.Uij hjk,
        ∃ u ∈ Work.EKLContract.Uij hik, h = g * u)
    ∧ (∀ h ∈ Work.EKLC7.VijIk hij hik, ∃ g ∈ Work.EKLContract.Uij hij,
        ∃ u ∈ Work.EKLContract.Uij hik, h = g * u)
    ∧ (∀ g ∈ Work.EKLContract.Uij hij, ∀ u ∈ Work.EKLC7.VjkIk hjk hik,
        g * u * g⁻¹ ∈ Work.EKLC7.VjkIk hjk hik)
    ∧ (∀ g ∈ Work.EKLContract.Uij hjk, ∀ u ∈ Work.EKLC7.VijIk hij hik,
        g * u * g⁻¹ ∈ Work.EKLC7.VijIk hij hik)
    ∧ (∀ g ∈ Work.EKLContract.Uij hjk, ∀ u ∈ Work.EKLContract.Uij hik,
        g * u * g⁻¹ ∈ Work.EKLContract.Uij hik)
    ∧ (∀ g ∈ Work.EKLContract.Uij hij, ∀ u ∈ Work.EKLContract.Uij hik,
        g * u * g⁻¹ ∈ Work.EKLContract.Uij hik)
    ∧ (∀ g : Work.EKLContract.SL3, g ∈ Work.EKLContract.Uij hij →
        g ∈ Work.EKLC7.VjkIk hjk hik → g = 1)
    ∧ (∀ g : Work.EKLContract.SL3, g ∈ Work.EKLContract.Uij hjk →
        g ∈ Work.EKLC7.VijIk hij hik → g = 1)
    ∧ (∀ g : Work.EKLContract.SL3, g ∈ Work.EKLContract.Uij hjk →
        g ∈ Work.EKLContract.Uij hik → g = 1)
    ∧ (∀ g : Work.EKLContract.SL3, g ∈ Work.EKLContract.Uij hij →
        g ∈ Work.EKLContract.Uij hik → g = 1) := by
  intro i j k hij hjk hik
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun g => mem_Heis3_iff hij hjk hik g
  · show Uij hij ≤ (Uij hij ⊔ Uij hjk) ⊔ Uij hik
    exact le_trans le_sup_left le_sup_left
  · show Uij hjk ≤ (Uij hij ⊔ Uij hjk) ⊔ Uij hik
    exact le_trans le_sup_right le_sup_left
  · show Uij hik ≤ (Uij hij ⊔ Uij hjk) ⊔ Uij hik
    exact le_sup_right
  · exact le_sup_left
  · exact le_sup_right
  · exact le_sup_left
  · exact le_sup_right
  · exact centre_Uik hij hjk hik
  · exact split_VjkIk hij hjk hik
  · exact split_VijIk hij hjk hik
  · exact split_VjkIk_2 hij hjk hik
  · exact split_VijIk_2 hij hjk hik
  · exact normalize_14 hij hjk hik
  · exact normalize_15 hij hjk hik
  · exact normalize_16 hij hjk hik
  · exact normalize_17 hij hjk hik
  · exact disjoint_Uij_VjkIk hij hjk hik
  · exact disjoint_Ujk_VijIk hij hjk hik
  · exact disjoint_Ujk_Uik hij hjk hik
  · exact disjoint_Uij_Uik hij hjk hik

end Work.EKLC7
