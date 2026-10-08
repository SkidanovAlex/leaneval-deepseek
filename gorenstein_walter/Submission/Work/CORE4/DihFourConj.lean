import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.DihFourConjAux.exists_rot_conj_mul_center
import Submission.Work.CORE4.DihFourConjAux.center_involution_eq_centralRotation
import Submission.Work.CORE4.DihFourConjAux.exists_sylow_le_centralizer
import Submission.Work.CORE4.DihFourConjAux.isFourGroup_closure_pair

open Subgroup
open scoped Pointwise

namespace Work.CORE4

/-- Arithmetic: if `2 * n` is a power of two and `n ≥ 4`, then `4 ∣ n`.

(`S ≅ DihedralGroup n` with `S` a `2`-group forces `2 * n = 2 ^ k`; `n ≥ 4` then forces `k ≥ 3`,
so `n = 2 ^ (k - 1)` is divisible by `4`.) -/
private theorem four_dvd_of_two_mul_eq_two_pow {n k : ℕ} (h : 2 * n = 2 ^ k) (hn : 4 ≤ n) :
    4 ∣ n := by
  have hk3 : 3 ≤ k := by
    by_contra hc
    push Not at hc
    interval_cases k <;> omega
  have hn_eq : n = 2 ^ (k - 1) := by
    have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ']
    rw [← h] at h2
    exact Nat.mul_left_cancel (by norm_num) h2
  rw [hn_eq]
  simpa using Nat.pow_dvd_pow 2 (show 2 ≤ k - 1 by omega)

/-- **General leaf `DihFourConj`** (pure group theory, used by N5c).

`DihFourConjProp` : with `S` a Sylow 2-subgroup of a finite `G` with `S ≅ DihedralGroup n`, `n ≥ 4`,
all involutions of `G` conjugate, `t ∈ Z(S)` an involution and `r ∈ S` an involution `≠ t`, there is
`y ∈ C_G(t·r)` with `y r y⁻¹ = t`.

Proof (reviewed, both critics): `⟨t,r⟩ ≅ V₄`, `tr` is an involution, `tr ∼ t`, so
`|C(tr)|₂ = |C(t)|₂ = |S|`; a Sylow `T ≤ C(tr)` containing `⟨t,r⟩` is a Sylow of `G`, hence dihedral
with `tr = z` central; `n/2` is even (as `n ≥ 4` is a power of 2), so `t` and `r = t·z` are
reflections of `D_{2n}` and lie in one `T`-class; take `y ∈ T`. -/
theorem DihFourConj : Work.GW2.DihFourConjProp := by
  intro G _ _ S n hn4 hSiso hconj t htS ht2 htcent r hrS hr2 hrne
  classical
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨φ⟩ := hSiso
  -- ### basic involution facts
  have ht_sq : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2] at h
  have hr_sq : r ^ 2 = 1 := by
    have h := pow_orderOf_eq_one r
    rwa [hr2] at h
  have ht_mul : t * t = 1 := by rwa [pow_two] at ht_sq
  have hr_mul : r * r = 1 := by rwa [pow_two] at hr_sq
  have ht_ne1 : t ≠ 1 := by intro h; rw [h, orderOf_one] at ht2; omega
  have hr_ne1 : r ≠ 1 := by intro h; rw [h, orderOf_one] at hr2; omega
  have hcomm : t * r = r * t := (htcent r hrS).symm
  have htr_mul : (t * r) * (t * r) = 1 := by
    rw [show (t * r) * (t * r) = t * (r * t) * r by group, ← hcomm,
      show t * (t * r) * r = (t * t) * (r * r) by group, ht_mul, hr_mul, one_mul]
  have htr_pow : (t * r) ^ 2 = 1 := by rwa [pow_two]
  have htr_ne1 : t * r ≠ 1 := by
    intro h
    have h1 : r = t⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht_mul
    exact hrne (by rw [h1, h2])
  have htr_ord : orderOf (t * r) = 2 := orderOf_eq_prime htr_pow htr_ne1
  -- ### a conjugate of `t` by the element sending `t` to `t * r`
  obtain ⟨g, hg⟩ : ∃ g : G, t * r = g * t * g⁻¹ := by
    obtain ⟨u, hu⟩ := hconj t (t * r) ht2 htr_ord
    refine ⟨(u : G), ?_⟩
    rw [SemiconjBy.eq hu]; group
  -- ### a Sylow 2-subgroup of `G` inside `C_G(t * r)`
  have hScent : ((g • S : Sylow 2 G) : Subgroup G) ≤
      Subgroup.centralizer ({t * r} : Set G) := by
    intro x hx
    rw [Sylow.coe_subgroup_smul] at hx
    obtain ⟨s, hsS, hxs⟩ := Subgroup.mem_map.mp hx
    have hx_eq : x = g * s * g⁻¹ := by
      rw [← hxs]
      simp only [MulDistribMulAction.toMonoidEnd_apply]
      exact MulAut.conj_apply g s
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [hx_eq, hg]
    have hts : t * s = s * t := (htcent s hsS).symm
    rw [show (g * t * g⁻¹) * (g * s * g⁻¹) = g * (t * s) * g⁻¹ by group,
      show (g * s * g⁻¹) * (g * t * g⁻¹) = g * (s * t) * g⁻¹ by group, hts]
  have hcent : ∃ T : Sylow 2 G, (T : Subgroup G) ≤ Subgroup.centralizer ({t * r} : Set G) :=
    ⟨g • S, hScent⟩
  -- ### the four-group `⟨t, r⟩` and a Sylow containing it
  have htC : t ∈ Subgroup.centralizer ({t * r} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show (t * r) * t = t * (t * r)
    calc (t * r) * t = t * (r * t) := by group
      _ = t * (t * r) := by rw [← hcomm]
  have hrC : r ∈ Subgroup.centralizer ({t * r} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show (t * r) * r = r * (t * r)
    calc (t * r) * r = t * (r * r) := by group
      _ = t := by rw [hr_mul, mul_one]
      _ = (r * r) * t := by rw [hr_mul, one_mul]
      _ = r * (r * t) := by group
      _ = r * (t * r) := by rw [← hcomm]
  have hWcent : Subgroup.closure ({t, r} : Set G) ≤ Subgroup.centralizer ({t * r} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact htC
    · exact hrC
  have hfour :=
    Work.CORE4.DihFourConjAux.isFourGroup_closure_pair ht_sq hr_sq hcomm ht_ne1 hr_ne1
      (fun h => hrne h.symm)
  obtain ⟨R, hWR, hRcent⟩ :=
    Work.CORE4.DihFourConjAux.exists_sylow_le_centralizer (Subgroup.closure ({t, r} : Set G))
      hfour.2.2 (t * r) hWcent hcent
  have htR : t ∈ (R : Subgroup G) := hWR (Subgroup.subset_closure (by simp))
  have hrR : r ∈ (R : Subgroup G) := hWR (Subgroup.subset_closure (by simp))
  haveI : Finite (Sylow 2 G) := Sylow.finite_of_finiteIndex S
  have ψR : (R : Subgroup G) ≃* DihedralGroup n := (Sylow.equiv S R).symm.trans φ
  let A : DihedralGroup n := ψR ⟨t, htR⟩
  let B : DihedralGroup n := ψR ⟨r, hrR⟩
  let Z : DihedralGroup n := ψR ⟨t * r, R.mul_mem htR hrR⟩
  have hA2 : A ^ 2 = 1 := by
    have h : (⟨t, htR⟩ : (R : Subgroup G)) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using ht_sq
    dsimp only [A]
    rw [← map_pow, h, map_one]
  have hA1 : A ≠ 1 := by
    intro h
    dsimp only [A] at h
    have h2 : (⟨t, htR⟩ : (R : Subgroup G)) = 1 := ψR.injective (by rw [h, map_one])
    exact ht_ne1 (by simpa using congrArg Subtype.val h2)
  have hZcenter : Z ∈ Subgroup.center (DihedralGroup n) := by
    have hZR : (⟨t * r, R.mul_mem htR hrR⟩ : (R : Subgroup G)) ∈
        Subgroup.center ((R : Subgroup G)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (Subgroup.mem_centralizer_iff.mp (hRcent y.2) (t * r) (Set.mem_singleton _)).symm
    dsimp only [Z]
    rw [Subgroup.mem_center_iff]
    intro d
    obtain ⟨d', rfl⟩ := ψR.surjective d
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hZR d']
  have hZ2 : Z ^ 2 = 1 := by
    have h : (⟨t * r, R.mul_mem htR hrR⟩ : (R : Subgroup G)) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using htr_pow
    dsimp only [Z]
    rw [← map_pow, h, map_one]
  have hZ1 : Z ≠ 1 := by
    intro h
    dsimp only [Z] at h
    have h2 : (⟨t * r, R.mul_mem htR hrR⟩ : (R : Subgroup G)) = 1 :=
      ψR.injective (by rw [h, map_one])
    exact htr_ne1 (by simpa using congrArg Subtype.val h2)
  have hZeq : Z = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) :=
    Work.CORE4.DihFourConjAux.center_involution_eq_centralRotation hn4 hZcenter hZ2 hZ1
  have hAZ : A * Z = B := by
    dsimp only [A, B, Z]
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show t * (t * r) = r
    calc t * (t * r) = (t * t) * r := by group
      _ = r := by rw [ht_mul, one_mul]
  have hAne : A ≠ DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
    intro h
    have hAZ' : A = Z := by rw [h, ← hZeq]
    have h2 : (⟨t, htR⟩ : (R : Subgroup G)) = ⟨t * r, R.mul_mem htR hrR⟩ := by
      apply ψR.injective
      rw [show ψR ⟨t, htR⟩ = A from rfl,
        show ψR ⟨t * r, R.mul_mem htR hrR⟩ = Z from rfl, hAZ']
    have h3 : t = t * r := by simpa using congrArg Subtype.val h2
    have hr1 : r = 1 := by
      have h4 : t * 1 = t * r := by rw [mul_one, ← h3]
      exact (mul_left_cancel h4).symm
    exact hr_ne1 hr1
  -- ### `4 ∣ n`
  obtain ⟨k, hk⟩ :=
    (IsPGroup.iff_card (p := 2) (G := ↥(S : Subgroup G))).1 S.isPGroup'
  have h2n : 2 * n = 2 ^ k := by
    rw [← DihedralGroup.nat_card (n := n), ← Nat.card_congr φ.toEquiv]
    exact hk
  have h4 : 4 ∣ n := four_dvd_of_two_mul_eq_two_pow h2n hn4
  -- ### the dihedral conjugacy
  obtain ⟨s, _hsrot, hconjs⟩ :=
    Work.CORE4.DihFourConjAux.exists_rot_conj_mul_center n h4 A hA2 hA1 hAne
  have hB : B = A * DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by rw [← hAZ, hZeq]
  have hconjBA : s⁻¹ * B * s = A := by
    rw [hB, hconjs.symm]
    group
  let yR : (R : Subgroup G) := ψR.symm s⁻¹
  have hyRs : ψR yR = s⁻¹ := ψR.apply_symm_apply s⁻¹
  have hconj_y : yR * ⟨r, hrR⟩ * yR⁻¹ = ⟨t, htR⟩ := by
    apply ψR.injective
    rw [map_mul, map_mul, map_inv, hyRs, inv_inv,
      show ψR ⟨r, hrR⟩ = B from rfl, show ψR ⟨t, htR⟩ = A from rfl]
    exact hconjBA
  refine ⟨(yR : G), hRcent yR.2, ?_⟩
  have h5 := congrArg (fun z : (R : Subgroup G) => (z : G)) hconj_y
  simpa using h5

end Work.CORE4
