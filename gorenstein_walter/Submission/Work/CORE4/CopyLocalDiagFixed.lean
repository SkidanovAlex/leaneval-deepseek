import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.ProjOfInfBot

/-!
# A repaired form of `Work.CORE4.CopyLocalDiag`

`Work.CORE4.CopyLocalDiag` is **false** as stated (see `Submission/Work/CORE4/CopyLocalDiag.lean`
for the statement and `scratch_cld/probe.lean` in the workspace root for a machine-checked
counterexample: `G = S₃ × S₃`, `P = S₃ × 1`, `E = 1 × S₃`, `p = 3`, `a = (c,1)`, `t = (1,c)`,
`n = (s,s)` with `s c s⁻¹ = c²`; then `n ∈ N(⟨a t⟩) ⊓ (P ⊔ E)` but
`n ∉ P ⊔ (E ⊓ C(⟨t⟩))`).

The defect is the **missing hypothesis that `a` centralises `P`**: in the intended application
(`CopyLocalProp`, Bender §4) `P₀` has order `p` and `a` generates it, so this is automatic.
All the results below carry the extra hypothesis `hacent : ∀ x ∈ P, x * a = a * x`
(or fewer: the first conjunct does not even need it).

Note also that the *first* conjunct of `CopyLocalDiag` is true as stated — only the second fails.
-/

namespace Work.CORE4

variable {G : Type*} [Group G]

/-- Every element of `P ⊔ E` is a product `p * e` with `p ∈ P`, `e ∈ E`, whenever the two
subgroups commute elementwise.  (Reproved here because the copy in `ProjOfInfBot` is `private`.) -/
theorem mem_sup_iff_prod (P E : Subgroup G)
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) :
    ∀ x : G, x ∈ (P ⊔ E : Subgroup G) ↔ ∃ p ∈ P, ∃ e ∈ E, p * e = x := by
  have hPcent : ∀ x ∈ P, x ∈ Subgroup.centralizer (E : Set G) :=
    fun x hx => Subgroup.mem_centralizer_iff.mpr (fun h hh => (hcomm x hx h hh).symm)
  have hLE : P ≤ Subgroup.normalizer (E : Set G) :=
    fun x hx => Subgroup.centralizer_le_normalizer (E : Set G) (hPcent x hx)
  intro x
  constructor
  · intro hx
    have hx' : x ∈ (↑(P ⊔ E) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P E hLE] at hx'
    exact Set.mem_mul.mp hx'
  · rintro ⟨p, hp, e, he, rfl⟩
    exact Subgroup.mul_mem_sup hp he

/-- Key step.  If `a * t' ∈ ⟨a * t⟩` with `a ∈ P`, `t, t' ∈ E`, `P` and `E` commuting with
`P ⊓ E = ⊥` and `orderOf a = orderOf t = p`, then `t' = t`. -/
theorem eq_of_mul_mem_zpowers (P E : Subgroup G)
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) (hinf : P ⊓ E = ⊥)
    {p : ℕ} {a t t' : G} (ha : a ∈ P) (ht : t ∈ E) (ht' : t' ∈ E)
    (hord_a : orderOf a = p) (hord_t : orderOf t = p)
    (h : a * t' ∈ Subgroup.zpowers (a * t)) : t' = t := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  have hcomm_at : Commute a t := hcomm a ha t ht
  have hmul : a ^ m * t ^ m = a * t' := by
    rw [← Commute.mul_zpow hcomm_at m, hm]
  have hE : t' * (t ^ m)⁻¹ ∈ E := E.mul_mem ht' (E.inv_mem (E.zpow_mem ht m))
  have h2 : a ^ m = a * (t' * (t ^ m)⁻¹) := by
    calc a ^ m = a ^ m * t ^ m * (t ^ m)⁻¹ := by group
      _ = (a * t') * (t ^ m)⁻¹ := by rw [hmul]
      _ = a * (t' * (t ^ m)⁻¹) := by group
  have hkey : a ^ (m - 1) = t' * (t ^ m)⁻¹ := by
    have hcy : a * (t' * (t ^ m)⁻¹) = (t' * (t ^ m)⁻¹) * a :=
      hcomm a ha (t' * (t ^ m)⁻¹) hE
    calc a ^ (m - 1) = a ^ m * a⁻¹ := zpow_sub_one a m
      _ = (a * (t' * (t ^ m)⁻¹)) * a⁻¹ := by rw [h2]
      _ = ((t' * (t ^ m)⁻¹) * a) * a⁻¹ := by rw [hcy]
      _ = t' * (t ^ m)⁻¹ := by group
  have hone : a ^ (m - 1) = 1 := by
    have hmem : a ^ (m - 1) ∈ P ⊓ E :=
      ⟨P.zpow_mem ha (m - 1), by rw [hkey]; exact hE⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hmem
  have ht'm : t' = t ^ m := mul_inv_eq_one.mp (by rw [← hkey, hone])
  have hpm : (p : ℤ) ∣ (m - 1) := by
    rw [← hord_a]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hone
  have htm : t ^ (m - 1) = 1 := by
    have : (orderOf t : ℤ) ∣ (m - 1) := by rw [hord_t]; exact hpm
    exact orderOf_dvd_iff_zpow_eq_one.mp this
  have htm' : t ^ m = t := by
    have hm1 : m = (m - 1) + 1 := by ring
    rw [hm1, zpow_add, htm, one_mul, zpow_one]
  rw [ht'm, htm']

/-- First conjunct of `CopyLocalDiag`; true as stated (no centrality of `a` in `P` needed). -/
theorem normalizer_diag_iff (P E : Subgroup G)
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) (hinf : P ⊓ E = ⊥)
    {p : ℕ} {a t : G} (ha : a ∈ P) (ht : t ∈ E)
    (hord_a : orderOf a = p) (hord_t : orderOf t = p) :
    ∀ e ∈ E, e ∈ Subgroup.normalizer (Subgroup.zpowers (a * t) : Set G) ↔
      e ∈ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
  intro e he
  constructor
  · intro hN
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hconj : e * (a * t) * e⁻¹ = a * (e * t * e⁻¹) := by
      rw [show e * (a * t) * e⁻¹ = (e * a) * t * e⁻¹ by group, ← hcomm a ha e he]
      group
    have hmem' : e * (a * t) * e⁻¹ ∈ Subgroup.zpowers (a * t) :=
      (Subgroup.mem_normalizer_iff.mp hN (a * t)).mp (Subgroup.mem_zpowers (a * t))
    have hmem : a * (e * t * e⁻¹) ∈ Subgroup.zpowers (a * t) := by
      rw [← hconj]; exact hmem'
    have ht' : e * t * e⁻¹ ∈ E := E.mul_mem (E.mul_mem he ht) (E.inv_mem he)
    have het : e * t = t * e := by
      have h1 := eq_of_mul_mem_zpowers P E hcomm hinf ha ht ht' hord_a hord_t hmem
      calc e * t = (e * t * e⁻¹) * e := by group
        _ = t * e := by rw [h1]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← hk]
    exact ((show Commute t e from het.symm).zpow_left k).eq
  · intro hC
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have het : Commute e t :=
      ((Subgroup.mem_centralizer_iff.mp hC) t (Subgroup.mem_zpowers t)).symm
    have hce_a : Commute e a := (hcomm a ha e he).symm
    have hce_at : Commute e (a * t) := hce_a.mul_right het
    have hce_inv : Commute e⁻¹ (a * t) := by
      have h := hce_at.eq
      calc e⁻¹ * (a * t) = e⁻¹ * ((a * t) * e) * e⁻¹ := by group
        _ = e⁻¹ * (e * (a * t)) * e⁻¹ := by rw [← h]
        _ = (a * t) * e⁻¹ := by group
    have hfix : ∀ w ∈ Subgroup.zpowers (a * t), e * w * e⁻¹ = w := by
      intro w hw
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← hk]
      calc e * (a * t) ^ k * e⁻¹ = ((a * t) ^ k * e) * e⁻¹ := by
            rw [(hce_at.zpow_right k).eq]
        _ = (a * t) ^ k := by group
    have hfix' : ∀ w ∈ Subgroup.zpowers (a * t), e⁻¹ * w * e = w := by
      intro w hw
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← hk]
      calc e⁻¹ * (a * t) ^ k * e = ((a * t) ^ k * e⁻¹) * e := by
            rw [(hce_inv.zpow_right k).eq]
        _ = (a * t) ^ k := by group
    constructor
    · intro hh; rw [hfix h hh]; exact hh
    · intro hh
      have h1 : h = e⁻¹ * (e * h * e⁻¹) * e := by group
      rw [h1, hfix' _ hh]
      exact hh

/-- **Repaired `CopyLocalDiag`.**  The only change is the added hypothesis `hacent` that `a`
centralises `P` (automatic when `P = ⟨a⟩`, e.g. `Nat.card P = p` in the intended application). -/
theorem CopyLocalDiagFixed (P E : Subgroup G)
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) (hinf : P ⊓ E = ⊥)
    {p : ℕ} {a t : G} (ha : a ∈ P) (ht : t ∈ E)
    (hacent : ∀ x ∈ P, x * a = a * x)
    (hord_a : orderOf a = p) (hord_t : orderOf t = p) :
    (∀ e ∈ E, e ∈ Subgroup.normalizer (Subgroup.zpowers (a * t) : Set G) ↔
        e ∈ Subgroup.centralizer (Subgroup.zpowers t : Set G)) ∧
      Subgroup.normalizer (Subgroup.zpowers (a * t) : Set G) ⊓ (P ⊔ E) ≤
        P ⊔ (E ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) := by
  refine ⟨normalizer_diag_iff P E hcomm hinf ha ht hord_a hord_t, ?_⟩
  intro n hn
  obtain ⟨hnN, hnSup⟩ := Subgroup.mem_inf.mp hn
  obtain ⟨p₀, hp₀, e, he, hpe⟩ := (mem_sup_iff_prod P E hcomm n).mp hnSup
  have hE : e * t * e⁻¹ ∈ E := E.mul_mem (E.mul_mem he ht) (E.inv_mem he)
  have hconj : p₀ * e * (a * t) * (p₀ * e)⁻¹ = a * (e * t * e⁻¹) := by
    have hpa : p₀ * a * p₀⁻¹ = a := by
      rw [hacent p₀ hp₀]; group
    have hpt : p₀ * (e * t * e⁻¹) * p₀⁻¹ = e * t * e⁻¹ := by
      rw [hcomm p₀ hp₀ (e * t * e⁻¹) hE]; group
    calc p₀ * e * (a * t) * (p₀ * e)⁻¹
        = p₀ * (e * a) * t * e⁻¹ * p₀⁻¹ := by group
      _ = p₀ * (a * e) * t * e⁻¹ * p₀⁻¹ := by rw [← hcomm a ha e he]
      _ = (p₀ * a * p₀⁻¹) * (p₀ * (e * t * e⁻¹) * p₀⁻¹) := by group
      _ = a * (e * t * e⁻¹) := by rw [hpa, hpt]
  have hmem' : n * (a * t) * n⁻¹ ∈ Subgroup.zpowers (a * t) :=
    (Subgroup.mem_normalizer_iff.mp hnN (a * t)).mp (Subgroup.mem_zpowers (a * t))
  have hmem : a * (e * t * e⁻¹) ∈ Subgroup.zpowers (a * t) := by
    rw [← hpe] at hmem'
    rw [hconj] at hmem'
    exact hmem'
  have hteq : e * t * e⁻¹ = t :=
    eq_of_mul_mem_zpowers P E hcomm hinf ha ht hE hord_a hord_t hmem
  have heC : e ∈ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← hk]
    have het : e * t = t * e := by
      calc e * t = (e * t * e⁻¹) * e := by group
        _ = t * e := by rw [hteq]
    exact ((show Commute t e from het.symm).zpow_left k).eq
  rw [← hpe]
  exact Subgroup.mul_mem_sup hp₀ ⟨he, heC⟩

end Work.CORE4
