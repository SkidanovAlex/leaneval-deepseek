import Mathlib
import Submission.Work.Coherence.Defs
import Submission.Work.Coherence.coherent_of_norm_two_lift
import Submission.Work.CharCore.Basic
import Submission.Work.Coherence.All
import Submission.Work.CharCore.Coherence
import Submission.Work.CharCore.cfInner_int_vchar
import Submission.Work.CharCore.cfInner_self_vchar_nat
import Submission.Work.FeitSibley.Coherence.arith_sum_sq_lt
import Submission.Work.FeitSibley.Coherence.int_mul_one_sub_nonneg

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.coherent_union_singleton`

Isaacs, *Character Theory of Finite Groups*, Theorem 7.14 (Feit) / Peterfalvi II, App. XII,
Lemme 1(a): if `(S₀, τ)` is coherent, `χ ∉ S₀`, `χ ∈ Irr H`, `τ` is an isometry on `ℤ[S₀ ∪ {χ}]⁰`
sending it to degree-zero virtual characters of `G`, and there is `ψ ∈ S₀` with `ψ(1) ∣ χ(1)` and
`2 ψ(1) χ(1) < ∑_{ξ∈S₀} ξ(1)²`, then `(S₀ ∪ {χ}, τ)` is coherent.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

open Work.Coherence

variable {H G : Type*}

/-- Membership in the lattice spanned by a single function: the integral multiples of that
function. -/
theorem mem_zSpan_singleton [Group G] [Fintype G] {x f : G → ℂ} :
    f ∈ Work.Coherence.ZSpan ({x} : Finset (G → ℂ)) ↔ ∃ m : ℤ, m • x = f := by
  rw [Work.Coherence.zSpan_singleton, AddSubgroup.mem_closure_singleton]

/-- A function orthogonal to every element of `S` is orthogonal to the whole lattice `ℤ[S]`. -/
theorem cfInner_eq_zero_of_mem_zSpan [Group G] [Fintype G] {S : Finset (G → ℂ)}
    {g : G → ℂ} (h : ∀ x ∈ S, cfInner x g = 0) :
    ∀ f ∈ Work.Coherence.ZSpan S, cfInner f g = 0 := by
  intro f hf
  obtain ⟨c, rfl⟩ := Work.Coherence.mem_zSpan.mp hf
  rw [cfInner_sum_left]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [cfInner_smul_left, h x x.2, mul_zero]

/-- Evaluation of an integral multiple of a complex number. -/
theorem zsmul_complex (m : ℤ) (z : ℂ) : m • z = (m : ℂ) * z :=
  zsmul_eq_mul z m

/-- Evaluation of an integral multiple of a complex-valued function. -/
theorem zsmul_fun_apply {H : Type*} (m : ℤ) (f : H → ℂ) (x : H) :
    (m • f) x = (m : ℂ) * f x := by
  rw [Pi.smul_apply, zsmul_complex]

theorem coherent_union_singleton {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S0 : Finset (H → ℂ)} {chi : H → ℂ} {tau : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hchi : chi ∉ S0)
    (hIrr : ∀ xi ∈ S0 ∪ {chi}, xi ∈ Work.CharCore.Irr H)
    (htau : Work.Coherence.IsometryOn (S0 ∪ {chi}) tau)
    (htauV : ∀ alpha ∈ Work.Coherence.ZSpan0 (S0 ∪ {chi}),
      Work.Coherence.IsVChar (tau alpha) ∧ tau alpha 1 = 0)
    (hcoh : Work.Coherence.Coherent S0 tau)
    (hpsi : ∃ psi ∈ S0, ∃ d : ℕ, chi 1 = (d : ℂ) * psi 1 ∧
      2 * (Work.CharCore.irrDeg psi) * (Work.CharCore.irrDeg chi)
        < ∑ xi ∈ S0, (Work.CharCore.irrDeg xi) ^ 2) :
    Work.Coherence.Coherent (S0 ∪ {chi}) tau := by
  classical
  obtain ⟨psi, hpsi_mem, d, hd_deg, hdeg_ineq⟩ := hpsi
  have hIrr_S0 : ∀ xi ∈ S0, xi ∈ Work.CharCore.Irr H :=
    fun xi h => hIrr xi (Finset.mem_union_left _ h)
  have hchi_irr : chi ∈ Work.CharCore.Irr H :=
    hIrr chi (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hpsi_irr : psi ∈ Work.CharCore.Irr H := hIrr_S0 psi hpsi_mem
  have hIrrS0' : ∀ xi ∈ S0, xi ∈ Irr H :=
    fun xi h => (Work.CharCore.mem_Irr_iff_coherence).mp (hIrr_S0 xi h)
  have hchiIrr' : chi ∈ Irr H := (Work.CharCore.mem_Irr_iff_coherence).mp hchi_irr
  have hpsiIrr' : psi ∈ Irr H := (Work.CharCore.mem_Irr_iff_coherence).mp hpsi_irr
  have hS0orth : Orthonormal S0 := irr_orthonormal_finset (fun x hx => hIrrS0' x hx)
  have hpsi1 : psi 1 = (Work.CharCore.irrDeg psi : ℂ) := Work.CharCore.irrDeg_spec hpsi_irr
  have hchi1 : chi 1 = (Work.CharCore.irrDeg chi : ℂ) := Work.CharCore.irrDeg_spec hchi_irr
  have hpsi1_ne : psi 1 ≠ 0 := by
    rw [hpsi1]; exact_mod_cast Work.CharCore.irrDeg_ne_zero hpsi_irr
  have hchipsi : chi ≠ psi := fun h => hchi (h ▸ hpsi_mem)
  have hdegrel : Work.CharCore.irrDeg chi = d * Work.CharCore.irrDeg psi := by
    have h : (Work.CharCore.irrDeg chi : ℂ) = (d : ℂ) * (Work.CharCore.irrDeg psi : ℂ) := by
      rw [← hchi1, ← hpsi1, hd_deg]
    have h' : (Work.CharCore.irrDeg chi : ℂ)
        = ((d * Work.CharCore.irrDeg psi : ℕ) : ℂ) := by
      rw [h]; push_cast; ring
    exact_mod_cast h'
  have hd_ne : d ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, zero_mul] at hd_deg
    exact Work.CharCore.irrDeg_ne_zero hchi_irr (by rw [← hchi1, hd_deg])
  have hd_pos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd_ne
  have hpi_pos : (0 : ℤ) < (Work.CharCore.irrDeg psi : ℤ) := by
    exact_mod_cast Work.CharCore.irrDeg_pos hpsi_irr
  have hpi_ne : (Work.CharCore.irrDeg psi : ℤ) ≠ 0 := ne_of_gt hpi_pos
  obtain ⟨taustar, htau'_agree, htau'_iso, htau'_vchar⟩ := hcoh
  -- the degree-zero element `χ - dψ`
  set g0 : H → ℂ := chi - (d : ℂ) • psi with hg0_def
  have hg0_mem_S : g0 ∈ ZSpan0 (S0 ∪ {chi}) := by
    rw [hg0_def, mem_zSpan0]
    refine ⟨?_, ?_⟩
    · have hchi_mem : chi ∈ ZSpan (S0 ∪ {chi}) :=
        self_mem_zSpan (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      have hpsi_mem' : psi ∈ ZSpan (S0 ∪ {chi}) :=
        self_mem_zSpan (Finset.mem_union_left _ hpsi_mem)
      have hdpsi : (d : ℂ) • psi = (d : ℤ) • psi := Int.cast_smul_eq_zsmul ℂ d psi
      rw [hdpsi]
      exact AddSubgroup.sub_mem _ hchi_mem (AddSubgroup.zsmul_mem _ hpsi_mem' d)
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hd_deg]; ring
  set u : G → ℂ := tau g0 with hu_def
  have huV : IsVChar u ∧ u 1 = 0 := htauV g0 hg0_mem_S
  set w : G → ℂ := (d : ℂ) • (taustar psi) with hw_def
  have hwV : IsVChar w := by
    have hz : (d : ℂ) • (taustar psi) = (d : ℤ) • (taustar psi) :=
      Int.cast_smul_eq_zsmul ℂ d (taustar psi)
    rw [hw_def, hz]
    exact (htau'_vchar psi hpsi_mem).zsmul (d : ℤ)
  -- the coefficients `b`
  have hb_exists : ∀ eta : ↥S0, ∃ n : ℤ, cfInner (u + w) (taustar (eta : H → ℂ)) = (n : ℂ) := by
    intro eta
    have h1 : Work.CharCore.IsVChar (u + w) :=
      (Work.CharCore.IsVChar_iff_coherence (u + w)).mpr (huV.1.add hwV)
    have h2 : Work.CharCore.IsVChar (taustar (eta : H → ℂ)) :=
      (Work.CharCore.IsVChar_iff_coherence _).mpr (htau'_vchar (eta : H → ℂ) eta.2)
    exact Work.CharCore.cfInner_int_vchar h1 h2
  set b : ↥S0 → ℤ := fun eta => Classical.choose (hb_exists eta) with hb_def
  have hb_spec : ∀ eta : ↥S0, cfInner (u + w) (taustar (eta : H → ℂ)) = (b eta : ℂ) :=
    fun eta => Classical.choose_spec (hb_exists eta)
  set Ssum : G → ℂ := ∑ eta : ↥S0, (b eta : ℂ) • (taustar (eta : H → ℂ)) with hSsum_def
  set Ssq : ℤ := ∑ eta : ↥S0, (b eta) ^ 2 with hSsq_def
  set Delt : G → ℂ := u + w - Ssum with hDelt_def
  have hDeltV : IsVChar Delt := by
    rw [hDelt_def]
    refine (huV.1.add hwV).sub ?_
    rw [hSsum_def]
    refine IsVChar.sum _ (fun eta => (b eta : ℂ) • (taustar (eta : H → ℂ))) ?_
    intro eta _
    have hz : (b eta : ℂ) • (taustar (eta : H → ℂ)) = (b eta : ℤ) • (taustar (eta : H → ℂ)) :=
      Int.cast_smul_eq_zsmul ℂ (b eta) _
    rw [hz]
    exact (htau'_vchar (eta : H → ℂ) eta.2).zsmul (b eta)
  -- pairwise inner products of the images of `S₀`
  have horth_pair : ∀ eta xi : ↥S0, cfInner (taustar (eta : H → ℂ)) (taustar (xi : H → ℂ))
      = if eta = xi then 1 else 0 := by
    intro eta xi
    rw [htau'_iso.inner_eq (eta : H → ℂ) (self_mem_zSpan eta.2) (xi : H → ℂ) (self_mem_zSpan xi.2)]
    rw [irr_cfInner (hIrrS0' eta eta.2) (hIrrS0' xi xi.2)]
    by_cases h : eta = xi
    · subst h; simp
    · have h' : ¬ ((eta : H → ℂ) = (xi : H → ℂ)) := fun hh => h (Subtype.ext hh)
      rw [if_neg h', if_neg h]
  have horth : ∀ eta : ↥S0, cfInner Delt (taustar (eta : H → ℂ)) = 0 := by
    intro eta
    have hsum : cfInner (∑ xi : ↥S0, (b xi : ℂ) • (taustar (xi : H → ℂ)))
        (taustar (eta : H → ℂ)) = (b eta : ℂ) := by
      rw [cfInner_sum_left]
      have hstep : ∀ xi : ↥S0, cfInner ((b xi : ℂ) • (taustar (xi : H → ℂ)))
          (taustar (eta : H → ℂ)) = (b xi : ℂ) * (if xi = eta then 1 else 0) := by
        intro xi; rw [cfInner_smul_left, horth_pair xi eta]
      rw [Finset.sum_congr rfl (fun xi _ => hstep xi)]
      rw [Finset.sum_eq_single eta]
      · simp
      · intro xi _ hxi; rw [if_neg hxi, mul_zero]
      · intro h; exact absurd (Finset.mem_univ eta) h
    rw [hDelt_def, cfInner_sub_left, hb_spec eta, hsum, sub_self]
  have horth' : ∀ eta : ↥S0, cfInner (taustar (eta : H → ℂ)) Delt = 0 := by
    intro eta
    rw [cfInner_conj_symm, horth eta, map_zero]
  -- `B = b ψ`
  set B : ℤ := b ⟨psi, hpsi_mem⟩ with hB_def
  have hb_psi : cfInner (u + w) (taustar psi) = (B : ℂ) := hb_spec ⟨psi, hpsi_mem⟩
  have hpp : cfInner (taustar psi) (taustar psi) = 1 := by
    have h := horth_pair ⟨psi, hpsi_mem⟩ ⟨psi, hpsi_mem⟩
    simpa using h
  -- norm computations
  have huu : cfInner u u = 1 + (d : ℂ) ^ 2 := by
    rw [hu_def, htau.inner_eq g0 hg0_mem_S g0 hg0_mem_S, hg0_def]
    simp only [cfInner_sub_left, cfInner_sub_right, cfInner_smul_left, cfInner_smul_right]
    rw [irr_cfInner hchiIrr' hchiIrr', irr_cfInner hchiIrr' hpsiIrr',
        irr_cfInner hpsiIrr' hchiIrr', irr_cfInner hpsiIrr' hpsiIrr']
    rw [if_pos rfl, if_neg hchipsi, if_neg (Ne.symm hchipsi), if_pos rfl]
    simp only [map_natCast]; ring
  have hww : cfInner w w = (d : ℂ) ^ 2 := by
    rw [hw_def, cfInner_smul_left, cfInner_smul_right, hpp, map_natCast]
    ring
  have hu_psi : cfInner u (taustar psi) = (B : ℂ) - (d : ℂ) := by
    have h1 : cfInner w (taustar psi) = (d : ℂ) := by
      rw [hw_def, cfInner_smul_left, hpp, mul_one]
    have h2 : (B : ℂ) = cfInner u (taustar psi) + (d : ℂ) := by
      rw [← hb_psi, cfInner_add_left, h1]
    rw [h2]; ring
  have hu_w : cfInner u w = (d : ℂ) * ((B : ℂ) - (d : ℂ)) := by
    rw [hw_def, cfInner_smul_right, hu_psi, map_natCast]
  have hw_u : cfInner w u = (d : ℂ) * ((B : ℂ) - (d : ℂ)) := by
    rw [cfInner_conj_symm w u, hu_w]
    have hBd : (B : ℂ) - (d : ℂ) = ((B - (d : ℤ) : ℤ) : ℂ) := by push_cast; ring
    rw [hBd]
    simp only [map_mul, map_natCast, map_intCast]
  have huw : cfInner (u + w) (u + w) = 1 + 2 * (d : ℂ) * (B : ℂ) := by
    rw [cfInner_add_left, cfInner_add_right, cfInner_add_right, huu, hu_w, hw_u, hww]
    ring
  -- equation (2)
  have hDelt_norm : cfInner Delt Delt = 1 + 2 * (d : ℂ) * (B : ℂ) - (Ssq : ℂ) := by
    have hD_exp : Delt = (u + w) - Ssum := by rw [hDelt_def]
    have hSsum_Delt : cfInner Ssum Delt = 0 := by
      rw [hSsum_def, cfInner_sum_left]
      refine Finset.sum_eq_zero fun eta _ => ?_
      rw [cfInner_smul_left, horth' eta, mul_zero]
    have h3 : cfInner (u + w) Ssum = (Ssq : ℂ) := by
      rw [hSsum_def, cfInner_sum_right]
      have hstep : ∀ eta : ↥S0, cfInner (u + w) ((b eta : ℂ) • (taustar (eta : H → ℂ)))
          = (b eta : ℂ) ^ 2 := by
        intro eta
        rw [cfInner_smul_right, hb_spec eta, map_intCast]; ring
      rw [Finset.sum_congr rfl (fun eta _ => hstep eta)]
      rw [hSsq_def, Int.cast_sum]
      exact Finset.sum_congr rfl (fun eta _ => (Int.cast_pow (b eta) 2).symm)
    have huDelt : cfInner (u + w) Delt = 1 + 2 * (d : ℂ) * (B : ℂ) - (Ssq : ℂ) := by
      rw [hD_exp, cfInner_sub_right, h3, huw]
    have e1 : cfInner Delt Delt = cfInner (u + w) Delt - cfInner Ssum Delt := by
      nth_rewrite 1 [hD_exp]; rw [cfInner_sub_left]
    rw [e1, hSsum_Delt, sub_zero, huDelt]
  -- `Delt` is a virtual character of natural norm
  obtain ⟨nD, hnD⟩ := Work.CharCore.cfInner_self_vchar_nat
    ((Work.CharCore.IsVChar_iff_coherence Delt).mpr hDeltV)
  have hInt : (nD : ℤ) + Ssq = 1 + 2 * (d : ℤ) * B := by
    have hnDc : cfInner Delt Delt = (nD : ℂ) := hnD
    apply (Int.cast_inj (α := ℂ)).mp
    have h : (nD : ℂ) + (Ssq : ℂ) = 1 + 2 * (d : ℂ) * (B : ℂ) := by
      rw [← hnDc, hDelt_norm]; ring
    push_cast
    exact h
  -- `u = Delt - w + Ssum`
  have hu_exp : u = Delt - w + Ssum := by rw [hDelt_def]; abel
  -- the "row" `cfInner (τ* ξ) u`
  have hP : ∀ eta : ↥S0, cfInner (taustar (eta : H → ℂ)) u
      = (b eta : ℂ) - (d : ℂ) * (if eta = ⟨psi, hpsi_mem⟩ then 1 else 0) := by
    intro eta
    have hw1 : cfInner (taustar (eta : H → ℂ)) w
        = (d : ℂ) * (if eta = ⟨psi, hpsi_mem⟩ then 1 else 0) := by
      rw [hw_def, cfInner_smul_right, horth_pair eta ⟨psi, hpsi_mem⟩, map_natCast]
    have hS1 : cfInner (taustar (eta : H → ℂ)) Ssum = (b eta : ℂ) := by
      rw [hSsum_def, cfInner_sum_right]
      have hstep : ∀ xi : ↥S0, cfInner (taustar (eta : H → ℂ)) ((b xi : ℂ) • (taustar (xi : H → ℂ)))
          = (b xi : ℂ) * (if eta = xi then 1 else 0) := by
        intro xi; rw [cfInner_smul_right, horth_pair eta xi, map_intCast]
      rw [Finset.sum_congr rfl (fun xi _ => hstep xi)]
      rw [Finset.sum_eq_single eta]
      · simp
      · intro xi _ hxi; rw [if_neg (Ne.symm hxi), mul_zero]
      · intro h; exact absurd (Finset.mem_univ eta) h
    rw [hu_exp, cfInner_add_right, cfInner_sub_right, horth' eta, hw1, hS1]
    ring
  -- the relation `ψ(1) b ξ = ξ(1) B`
  have hrel : ∀ eta : ↥S0,
      (Work.CharCore.irrDeg psi : ℤ) * b eta = (Work.CharCore.irrDeg (eta : H → ℂ) : ℤ) * B := by
    intro eta
    set Xi : H → ℂ := (Work.CharCore.irrDeg psi : ℤ) • (eta : H → ℂ)
        - (Work.CharCore.irrDeg (eta : H → ℂ) : ℤ) • psi with hXi_def
    have hXi_mem0 : Xi ∈ ZSpan0 S0 := by
      rw [hXi_def, mem_zSpan0]
      refine ⟨?_, ?_⟩
      · exact AddSubgroup.sub_mem _
          (AddSubgroup.zsmul_mem _ (self_mem_zSpan eta.2) _)
          (AddSubgroup.zsmul_mem _ (self_mem_zSpan hpsi_mem) _)
      · have heta1 : (eta : H → ℂ) 1 = (Work.CharCore.irrDeg (eta : H → ℂ) : ℂ) :=
          Work.CharCore.irrDeg_spec (hIrr_S0 (eta : H → ℂ) eta.2)
        simp only [Pi.sub_apply, Pi.smul_apply, heta1, hpsi1, zsmul_complex]
        push_cast
        ring
    have hXi_mem : Xi ∈ ZSpan0 (S0 ∪ {chi}) := zSpan0_mono Finset.subset_union_left hXi_mem0
    have hXi_val : taustar Xi = (Work.CharCore.irrDeg psi : ℤ) • taustar (eta : H → ℂ)
        - (Work.CharCore.irrDeg (eta : H → ℂ) : ℤ) • taustar psi := by
      rw [hXi_def, map_sub, map_zsmul, map_zsmul]
    have key : cfInner (taustar Xi) u = cfInner Xi g0 := by
      rw [htau'_agree Xi hXi_mem0, hu_def]
      exact htau.inner_eq Xi hXi_mem g0 hg0_mem_S
    have heta_g0 : cfInner (eta : H → ℂ) g0
        = - (d : ℂ) * (if eta = ⟨psi, hpsi_mem⟩ then 1 else 0) := by
      rw [hg0_def, cfInner_sub_right, cfInner_smul_right,
          irr_cfInner (hIrrS0' (eta : H → ℂ) eta.2) hchiIrr',
          irr_cfInner (hIrrS0' (eta : H → ℂ) eta.2) hpsiIrr', map_natCast]
      rw [if_neg (fun h => hchi (by simpa [h] using eta.2))]
      by_cases h : eta = ⟨psi, hpsi_mem⟩
      · subst h; simp
      · have h' : ¬ ((eta : H → ℂ) = psi) := fun hh => h (Subtype.ext hh)
        rw [if_neg h', if_neg h]; ring
    have hpsi_g0 : cfInner psi g0 = - (d : ℂ) := by
      rw [hg0_def, cfInner_sub_right, cfInner_smul_right, irr_cfInner hpsiIrr' hchiIrr',
          irr_cfInner hpsiIrr' hpsiIrr', map_natCast, if_neg (Ne.symm hchipsi)]
      rw [if_pos rfl]; ring
    have hL : cfInner (taustar Xi) u
        = (Work.CharCore.irrDeg psi : ℂ)
            * ((b eta : ℂ) - (d : ℂ) * (if eta = ⟨psi, hpsi_mem⟩ then 1 else 0))
          - (Work.CharCore.irrDeg (eta : H → ℂ) : ℂ) * ((B : ℂ) - (d : ℂ)) := by
      rw [hXi_val, cfInner_sub_left, cfInner_zsmul_left, cfInner_zsmul_left,
          hP eta, hP ⟨psi, hpsi_mem⟩]
      simp only [hB_def, ite_true, mul_one, Int.cast_natCast]
    have hR : cfInner Xi g0
        = (Work.CharCore.irrDeg psi : ℂ)
            * (- (d : ℂ) * (if eta = ⟨psi, hpsi_mem⟩ then 1 else 0))
          - (Work.CharCore.irrDeg (eta : H → ℂ) : ℂ) * (- (d : ℂ)) := by
      rw [hXi_def, cfInner_sub_left, cfInner_zsmul_left, cfInner_zsmul_left,
          heta_g0, hpsi_g0]
      simp only [ite_true, mul_one, Int.cast_natCast]
    have hmain : (Work.CharCore.irrDeg psi : ℂ)
            * ((b eta : ℂ) - (d : ℂ) * (if eta = ⟨psi, hpsi_mem⟩ then 1 else 0))
          - (Work.CharCore.irrDeg (eta : H → ℂ) : ℂ) * ((B : ℂ) - (d : ℂ))
        = (Work.CharCore.irrDeg psi : ℂ)
            * (- (d : ℂ) * (if eta = ⟨psi, hpsi_mem⟩ then 1 else 0))
          - (Work.CharCore.irrDeg (eta : H → ℂ) : ℂ) * (- (d : ℂ)) := by
      rw [← hL, ← hR, key]
    have hiff : (if eta = ⟨psi, hpsi_mem⟩ then (1:ℂ) else 0) = (if eta = ⟨psi, hpsi_mem⟩ then 1 else 0) := rfl
    apply (Int.cast_inj (α := ℂ)).mp
    push_cast
    linear_combination hmain
  -- relation (5): `ξ*(1) ψ(1) = ψ*(1) ξ(1)`
  have hdegrel2 : ∀ eta : ↥S0,
      psi 1 * (taustar (eta : H → ℂ)) 1 = ((eta : H → ℂ) 1) * (taustar psi) 1 := by
    intro eta
    set Xi : H → ℂ := (Work.CharCore.irrDeg psi : ℤ) • (eta : H → ℂ)
        - (Work.CharCore.irrDeg (eta : H → ℂ) : ℤ) • psi with hXi_def
    have hXi_mem0 : Xi ∈ ZSpan0 S0 := by
      rw [hXi_def, mem_zSpan0]
      refine ⟨?_, ?_⟩
      · exact AddSubgroup.sub_mem _
          (AddSubgroup.zsmul_mem _ (self_mem_zSpan eta.2) _)
          (AddSubgroup.zsmul_mem _ (self_mem_zSpan hpsi_mem) _)
      · have heta1 : (eta : H → ℂ) 1 = (Work.CharCore.irrDeg (eta : H → ℂ) : ℂ) :=
          Work.CharCore.irrDeg_spec (hIrr_S0 (eta : H → ℂ) eta.2)
        simp only [Pi.sub_apply, Pi.smul_apply, heta1, hpsi1, zsmul_complex]
        push_cast
        ring
    have hXi_mem : Xi ∈ ZSpan0 (S0 ∪ {chi}) := zSpan0_mono Finset.subset_union_left hXi_mem0
    have hzero : (tau Xi) 1 = 0 := (htauV Xi hXi_mem).2
    rw [← htau'_agree Xi hXi_mem0, hXi_def, map_sub, map_zsmul, map_zsmul] at hzero
    have h0 : (Work.CharCore.irrDeg psi : ℂ) * (taustar (eta : H → ℂ) 1)
        = (Work.CharCore.irrDeg (eta : H → ℂ) : ℂ) * (taustar psi 1) := by
      have hz : (Work.CharCore.irrDeg psi : ℤ) • (taustar (eta : H → ℂ) 1)
          - (Work.CharCore.irrDeg (eta : H → ℂ) : ℤ) • (taustar psi 1) = 0 := by
        simpa only [Pi.sub_apply, Pi.smul_apply] using hzero
      rw [sub_eq_zero] at hz
      rw [zsmul_complex, zsmul_complex] at hz
      push_cast at hz
      exact hz
    rw [hpsi1, Work.CharCore.irrDeg_spec (hIrr_S0 (eta : H → ℂ) eta.2)]
    exact h0
  -- `(τ* ψ)(1) ≠ 0`
  have hA_ne : (taustar psi) 1 ≠ 0 := by
    obtain ⟨theta, htheta, hcase⟩ := vchar_norm_one (htau'_vchar psi hpsi_mem) hpp
    have htheta' : theta ∈ Work.CharCore.Irr G :=
      (Work.CharCore.mem_Irr_iff_coherence).mpr htheta
    have hdeg : theta 1 = (Work.CharCore.irrDeg theta : ℂ) := Work.CharCore.irrDeg_spec htheta'
    rcases hcase with h | h
    · rw [h, hdeg]
      exact_mod_cast Work.CharCore.irrDeg_ne_zero htheta'
    · rw [h]; simp only [Pi.neg_apply]
      rw [hdeg, neg_ne_zero]
      exact_mod_cast Work.CharCore.irrDeg_ne_zero htheta'
  -- integer form of the degree inequality
  have hineq : 2 * (d : ℤ) * (Work.CharCore.irrDeg psi : ℤ) ^ 2
      < ∑ eta : ↥S0, (Work.CharCore.irrDeg (eta : H → ℂ) : ℤ) ^ 2 := by
    have hnat : 2 * (d * Work.CharCore.irrDeg psi) * Work.CharCore.irrDeg psi
        < ∑ xi ∈ S0, (Work.CharCore.irrDeg xi) ^ 2 := by
      rw [← hdegrel]
      have hc : 2 * Work.CharCore.irrDeg chi * Work.CharCore.irrDeg psi
          = 2 * Work.CharCore.irrDeg psi * Work.CharCore.irrDeg chi := by ring
      rw [hc]; exact hdeg_ineq
    have hZ : ((2 * (d * Work.CharCore.irrDeg psi) * Work.CharCore.irrDeg psi : ℕ) : ℤ)
        < ((∑ xi ∈ S0, (Work.CharCore.irrDeg xi) ^ 2 : ℕ) : ℤ) := by exact_mod_cast hnat
    have hLHS : (2 * (d : ℤ) * (Work.CharCore.irrDeg psi : ℤ) ^ 2)
        = ((2 * (d * Work.CharCore.irrDeg psi) * Work.CharCore.irrDeg psi : ℕ) : ℤ) := by
      push_cast; ring
    have hR : (∑ eta : ↥S0, (Work.CharCore.irrDeg (eta : H → ℂ) : ℤ) ^ 2)
        = ((∑ xi ∈ S0, (Work.CharCore.irrDeg xi) ^ 2 : ℕ) : ℤ) := by
      rw [Finset.sum_coe_sort (s := S0)
        (f := fun a : H → ℂ => ((Work.CharCore.irrDeg a : ℕ) : ℤ) ^ 2)]
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl (fun x _ => (Nat.cast_pow (Work.CharCore.irrDeg x) 2).symm)
    rw [hLHS, hR]; exact hZ
  -- the contradiction
  have hB_zero : B = 0 := by
    by_contra hBne
    have hp_pos : (0 : ℤ) < (Work.CharCore.irrDeg psi : ℤ) := by
      exact_mod_cast Work.CharCore.irrDeg_pos hpsi_irr
    have hdZ_pos : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd_pos
    have hSsq_large : 2 * (d : ℤ) * B ^ 2 < Ssq := by
      rw [hSsq_def]
      exact arith_sum_sq_lt Finset.univ b
        (fun eta : ↥S0 => (Work.CharCore.irrDeg (eta : H → ℂ) : ℤ)) B
        (Work.CharCore.irrDeg psi : ℤ) (d : ℤ) hp_pos hdZ_pos hBne
        (fun eta _ => hrel eta) hineq
    have hnD_le : (nD : ℤ) ≤ 2 * (d : ℤ) * B * (1 - B) := by
      have h1 : (nD : ℤ) = 1 + 2 * (d : ℤ) * B - Ssq := by linarith [hInt]
      have h2 : 2 * (d : ℤ) * B ^ 2 + 1 ≤ Ssq := by omega
      rw [h1]; nlinarith
    have hprod : 0 ≤ B * (1 - B) := by
      nlinarith [hnD_le, (show (0 : ℤ) ≤ (nD : ℤ) by positivity), hdZ_pos]
    rcases int_mul_one_sub_nonneg hprod with hB0 | hB1
    · exact hBne hB0
    · have hnD0 : (nD : ℤ) = 0 := by
        rw [hB1] at hnD_le
        simp only [mul_one, sub_self, mul_zero] at hnD_le
        omega
      have hDelt_zero : Delt = 0 := by
        apply vchar_norm_zero hDeltV
        have hnDc : cfInner Delt Delt = (nD : ℂ) := hnD
        rw [hnDc]; exact_mod_cast hnD0
      -- equation (3)
      have h3eq : (∑ eta : ↥S0, (b eta : ℂ) * (taustar (eta : H → ℂ)) 1)
          - (d : ℂ) * (taustar psi) 1 + Delt 1 = 0 := by
        have h := huV.2
        rw [hu_exp] at h
        have hw1 : w 1 = (d : ℂ) * (taustar psi) 1 := by
          rw [hw_def]; simp only [Pi.smul_apply, smul_eq_mul]
        have hSsum1 : Ssum 1 = ∑ eta : ↥S0, (b eta : ℂ) * (taustar (eta : H → ℂ)) 1 := by
          rw [hSsum_def]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        simp only [Pi.add_apply, Pi.sub_apply] at h
        rw [hw1, hSsum1] at h
        linear_combination h
      have hsum_eq : (∑ eta : ↥S0, (b eta : ℂ) * (taustar (eta : H → ℂ)) 1)
          = (d : ℂ) * (taustar psi) 1 := by
        have h := h3eq
        rw [hDelt_zero] at h
        simp only [Pi.zero_apply, add_zero] at h
        linear_combination h
      -- multiply by `ψ(1)` and use relation (5)
      have hsum_b : (∑ eta : ↥S0, (b eta : ℂ) * ((eta : H → ℂ) 1))
          = (d : ℂ) * (psi 1) := by
        have h := congrArg (fun z => (psi 1) * z) hsum_eq
        rw [Finset.mul_sum] at h
        have hpoint : ∀ eta : ↥S0, psi 1 * ((b eta : ℂ) * (taustar (eta : H → ℂ)) 1)
            = (taustar psi) 1 * ((b eta : ℂ) * ((eta : H → ℂ) 1)) := by
          intro eta
          linear_combination (b eta : ℂ) * hdegrel2 eta
        rw [Finset.sum_congr rfl (fun eta _ => hpoint eta)] at h
        rw [← Finset.mul_sum] at h
        have hcomm : (psi 1) * ((d : ℂ) * (taustar psi) 1)
            = (taustar psi) 1 * ((d : ℂ) * (psi 1)) := by ring
        rw [hcomm] at h
        exact mul_left_cancel₀ hA_ne h
      -- convert to integers
      have hsum_Z : (∑ eta : ↥S0, b eta * (Work.CharCore.irrDeg (eta : H → ℂ) : ℤ))
          = (d : ℤ) * (Work.CharCore.irrDeg psi : ℤ) := by
        apply (Int.cast_inj (α := ℂ)).mp
        push_cast
        have hgoal : (∑ eta : ↥S0, (b eta : ℂ) * ((Work.CharCore.irrDeg (eta : H → ℂ)) : ℂ))
            = (∑ eta : ↥S0, (b eta : ℂ) * ((eta : H → ℂ) 1)) :=
          Finset.sum_congr rfl (fun eta _ =>
            (congrArg (fun z => (b eta : ℂ) * z)
              (Work.CharCore.irrDeg_spec (hIrr_S0 (eta : H → ℂ) eta.2))).symm)
        rw [hgoal, hpsi1.symm]
        exact hsum_b
      -- contradiction
      have hQ : (∑ eta : ↥S0, (Work.CharCore.irrDeg (eta : H → ℂ) : ℤ) ^ 2)
          = (d : ℤ) * (Work.CharCore.irrDeg psi : ℤ) ^ 2 := by
        have h1 : (Work.CharCore.irrDeg psi : ℤ)
              * (∑ eta : ↥S0, b eta * (Work.CharCore.irrDeg (eta : H → ℂ) : ℤ))
            = ∑ eta : ↥S0, (Work.CharCore.irrDeg (eta : H → ℂ) : ℤ) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun eta _ => ?_)
          have h := hrel eta
          rw [hB1, mul_one] at h
          linear_combination (Work.CharCore.irrDeg (eta : H → ℂ) : ℤ) * h
        rw [hsum_Z] at h1
        have h2 : (Work.CharCore.irrDeg psi : ℤ) * ((d : ℤ) * (Work.CharCore.irrDeg psi : ℤ))
            = (d : ℤ) * (Work.CharCore.irrDeg psi : ℤ) ^ 2 := by ring
        rw [h2] at h1
        exact h1.symm
      rw [hQ] at hineq
      have hpos : 0 < (d : ℤ) * (Work.CharCore.irrDeg psi : ℤ) ^ 2 := by
        have : (0:ℤ) < (Work.CharCore.irrDeg psi : ℤ)^2 := by positivity
        nlinarith [hdZ_pos, this]
      nlinarith [hineq, hpos]
  -- with `B = 0`, all `b` vanish, `Delt = u + w`, `cfInner Delt Delt = 1`
  have hb_zero : ∀ eta : ↥S0, b eta = 0 := by
    intro eta
    have h := hrel eta
    rw [hB_zero, mul_zero] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hpi_ne
    · exact h'
  have hSsum_zero : Ssum = 0 := by
    rw [hSsum_def]
    refine Finset.sum_eq_zero fun eta _ => ?_
    rw [hb_zero eta, Int.cast_zero, zero_smul]
  have hSsq_zero : Ssq = 0 := by
    rw [hSsq_def]
    refine Finset.sum_eq_zero fun eta _ => by rw [hb_zero eta, zero_pow (by norm_num)]
  have hDelt_self : cfInner Delt Delt = 1 := by
    rw [hDelt_norm, hB_zero, hSsq_zero]; ring
  -- the extension
  let innerChi : (H → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => cfInner f chi
      map_add' := fun f g => cfInner_add_left f g chi
      map_smul' := fun c f => cfInner_smul_left c f chi }
  let sigma : (H → ℂ) →ₗ[ℤ] (G → ℂ) :=
    taustar + (innerChi.restrictScalars ℤ).smulRight (Delt - taustar chi)
  have hsigma_apply : ∀ f : H → ℂ,
      sigma f = taustar f + cfInner f chi • (Delt - taustar chi) := by
    intro f
    simp only [sigma, innerChi, LinearMap.add_apply, LinearMap.smulRight_apply,
      LinearMap.restrictScalars_apply]
    rfl
  have hsigma_S0 : ∀ x ∈ S0, sigma x = taustar x := by
    intro x hx
    rw [hsigma_apply]
    have hxc : cfInner x chi = 0 := by
      rw [irr_cfInner (hIrrS0' x hx) hchiIrr']
      rw [if_neg (fun h => hchi (by simpa [h] using hx))]
    rw [hxc, zero_smul, add_zero]
  have hsigma_chi : sigma chi = Delt := by
    rw [hsigma_apply]
    have h1 : cfInner chi chi = 1 := by rw [irr_cfInner hchiIrr' hchiIrr']; simp
    rw [h1, one_smul]; abel
  have hsigma_iso : IsometryOnAll (S0 ∪ {chi}) sigma := by
    apply isometryOnAll_of_gram
    intro x hx y hy
    rcases Finset.mem_union.mp hx with hxS0 | hxchi
    · rcases Finset.mem_union.mp hy with hyS0 | hychi
      · rw [hsigma_S0 x hxS0, hsigma_S0 y hyS0]
        exact htau'_iso.inner_eq x (self_mem_zSpan hxS0) y (self_mem_zSpan hyS0)
      · rw [Finset.mem_singleton.mp hychi, hsigma_S0 x hxS0, hsigma_chi,
            horth' ⟨x, hxS0⟩, irr_cfInner (hIrrS0' x hxS0) hchiIrr']
        rw [if_neg (fun h => hchi (by simpa [h] using hxS0))]
    · rw [Finset.mem_singleton.mp hxchi]
      rcases Finset.mem_union.mp hy with hyS0 | hychi
      · rw [hsigma_chi, hsigma_S0 y hyS0, horth ⟨y, hyS0⟩,
            irr_cfInner hchiIrr' (hIrrS0' y hyS0)]
        rw [if_neg (fun h => hchi (by simpa [← h] using hyS0))]
      · rw [Finset.mem_singleton.mp hychi, hsigma_chi, hDelt_self,
            irr_cfInner hchiIrr' hchiIrr']
        simp
  have hvchar_sigma : ∀ x ∈ S0 ∪ {chi}, IsVChar (sigma x) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxS0 | hxchi
    · rw [hsigma_S0 x hxS0]; exact htau'_vchar x hxS0
    · rw [Finset.mem_singleton.mp hxchi, hsigma_chi]; exact hDeltV
  have hcoh_sigma : Coherent (S0 ∪ {chi}) sigma :=
    coherent_of_isometryOnAll hsigma_iso hvchar_sigma
  -- agreement of `sigma` and `tau` on `ℤ[S₀ ∪ {χ}]⁰`
  have hdecomp : ∀ f ∈ ZSpan (S0 ∪ {chi}), ∃ g ∈ ZSpan S0, ∃ m : ℤ, f = g + m • chi := by
    intro f hf
    have h1 : f ∈ ZSpan S0 ⊔ ZSpan ({chi} : Finset (H → ℂ)) := by
      rw [← zSpan_union]; exact hf
    obtain ⟨g, hg, h, hh, hgh⟩ := AddSubgroup.mem_sup.mp h1
    obtain ⟨m, hm⟩ := mem_zSpan_singleton.mp hh
    exact ⟨g, hg, m, by rw [← hgh, ← hm]⟩
  have hsigma_agree : ∀ f ∈ ZSpan0 (S0 ∪ {chi}), sigma f = tau f := by
    intro f hf
    obtain ⟨g, hg, m, hfm⟩ := hdecomp f hf.1
    set phi : H → ℂ := g + (m * (d : ℤ)) • psi with hphi_def
    have hphi_mem : phi ∈ ZSpan0 S0 := by
      rw [hphi_def, mem_zSpan0]
      refine ⟨?_, ?_⟩
      · exact AddSubgroup.add_mem _ hg
          (AddSubgroup.zsmul_mem _ (self_mem_zSpan hpsi_mem) (m * (d : ℤ)))
      · have hf1 : (g + m • chi) 1 = 0 := by rw [← hfm]; exact hf.2
        have hA : (g + m • chi) 1 = g 1 + (m : ℂ) * (chi 1) := by
          simp only [Pi.add_apply, zsmul_fun_apply]
        have hB : (g + (m * (d : ℤ)) • psi) 1 = g 1 + (m : ℂ) * ((d : ℂ) * (psi 1)) := by
          rw [Pi.add_apply, zsmul_fun_apply]
          push_cast
          ring
        rw [hB, ← hd_deg, ← hA]
        exact hf1
    have hsplit : f = phi + m • (chi - (d : ℂ) • psi) := by
      have hdd : (d : ℂ) • psi = (d : ℤ) • psi := Int.cast_smul_eq_zsmul ℂ d psi
      rw [hfm, hphi_def, hdd, smul_sub, smul_smul]
      abel
    have hphi_sigma : sigma phi = tau phi := by
      rw [hsigma_apply]
      have hpc : cfInner phi chi = 0 := by
        refine cfInner_eq_zero_of_mem_zSpan ?_ phi hphi_mem.1
        intro x hx
        rw [irr_cfInner (hIrrS0' x hx) hchiIrr']
        rw [if_neg (fun h => hchi (by simpa [h] using hx))]
      rw [hpc, zero_smul, add_zero]
      exact htau'_agree phi hphi_mem
    have hchi_sigma : sigma (chi - (d : ℂ) • psi) = tau (chi - (d : ℂ) • psi) := by
      have hdpsi : (d : ℂ) • psi = (d : ℤ) • psi := Int.cast_smul_eq_zsmul ℂ d psi
      have hsig : sigma ((d : ℂ) • psi) = (d : ℤ) • taustar psi := by
        rw [hdpsi]
        rw [show sigma ((d : ℤ) • psi) = (d : ℤ) • sigma psi from map_zsmul sigma d psi]
        rw [hsigma_S0 psi hpsi_mem]
      have hlhs : sigma (chi - (d : ℂ) • psi) = Delt - (d : ℤ) • taustar psi := by
        rw [map_sub, hsigma_chi, hsig]
      have hrhs : tau (chi - (d : ℂ) • psi) = u := by
        rw [← hg0_def, ← hu_def]
      rw [hlhs, hrhs]
      have hw_eq : (d : ℤ) • taustar psi = w :=
        (Int.cast_smul_eq_zsmul ℂ (d : ℤ) (taustar psi)).symm.trans hw_def.symm
      rw [hw_eq, hu_exp, hSsum_zero, add_zero]
    rw [hsplit]
    simp only [map_add, map_zsmul, hphi_sigma, hchi_sigma]
  exact (coherent_congr (fun f hf => (hsigma_agree f hf).symm)).mpr hcoh_sigma

end Work.FeitSibley.Coherence
