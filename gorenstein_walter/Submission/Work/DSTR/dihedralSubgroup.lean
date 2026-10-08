import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.Dihedral.Defs
import Submission.Work.DSTR.DihHelp.dih_lift_of_cyclic_rot
import Submission.Work.DSTR.DihHelp.dih_decomp_reflection
import Submission.Work.DSTR.DihHelp.dih_sr_conj_rot

open DihedralGroup

namespace Work.DSTR

noncomputable section

/-- If `H ≤ DihedralGroup n` contains a reflection `sr u` (so that `H` is not contained in the
rotation subgroup), then `H` is dihedral. -/
theorem dihedral_case (n : ℕ) (H : Subgroup (DihedralGroup n)) (u : ZMod n)
    (hsH : (sr u : DihedralGroup n) ∈ H)
    (hsu : (sr u : DihedralGroup n) ∉ Work.Dihedral.rot n) :
    ∃ m : ℕ, Nonempty (↥H ≃* DihedralGroup m) := by
  classical
  set R : Subgroup (DihedralGroup n) := H ⊓ Work.Dihedral.rot n with hRdef
  have hRH : R ≤ H := by rw [hRdef]; exact inf_le_left
  have hRrot : R ≤ Work.Dihedral.rot n := by rw [hRdef]; exact inf_le_right
  have hRcyc : IsCyclic ↥R := by
    rw [hRdef]
    exact isCyclic_of_injective (Subgroup.inclusion inf_le_right)
      (Subgroup.inclusion_injective inf_le_right)
  let m : ℕ := Nat.card ↥R
  let e : Multiplicative (ZMod m) ≃* ↥R := zmodCyclicMulEquiv hRcyc
  let sH : ↥H := ⟨sr u, hsH⟩
  let g : ZMod m → ↥H := fun i =>
    ⟨((e (Multiplicative.ofAdd i) : ↥R) : DihedralGroup n),
      hRH (e (Multiplicative.ofAdd i)).2⟩
  have hgval : ∀ j : ZMod m, ((g j : ↥H) : DihedralGroup n)
      = ((e (Multiplicative.ofAdd j) : ↥R) : DihedralGroup n) := fun _ => rfl
  have hsHval : ((sH : ↥H) : DihedralGroup n) = sr u := rfl
  have hgmul : ∀ i j : ZMod m, g i * g j = g (i + j) := by
    intro i j
    have h : (e (Multiplicative.ofAdd i) : ↥R) * (e (Multiplicative.ofAdd j) : ↥R)
        = e (Multiplicative.ofAdd (i + j)) := by
      rw [← map_mul]
      exact congrArg e (by simp : Multiplicative.ofAdd i * Multiplicative.ofAdd j
        = Multiplicative.ofAdd (i + j))
    exact Subtype.ext (congrArg (fun z : ↥R => (z : DihedralGroup n)) h)
  have hsH2 : sH * sH = 1 := by
    apply Subtype.ext
    show (sr u : DihedralGroup n) * sr u = (1 : DihedralGroup n)
    rw [sr_mul_self]
  have hSc : ∀ i : ZMod m, g i * sH = sH * g (-i) := by
    intro i
    have hx : ∃ t : ZMod n, ((e (Multiplicative.ofAdd i) : ↥R) : DihedralGroup n) = r t :=
      (Work.Dihedral.mem_rot).mp (hRrot (e (Multiplicative.ofAdd i)).2)
    obtain ⟨_, h2⟩ := DihHelp.dih_sr_conj_rot u hx
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    show ((e (Multiplicative.ofAdd i) : ↥R) : DihedralGroup n) * sr u
        = sr u * ((e (Multiplicative.ofAdd (-i)) : ↥R) : DihedralGroup n)
    rw [show ((e (Multiplicative.ofAdd (-i)) : ↥R) : DihedralGroup n)
        = (((e (Multiplicative.ofAdd i) : ↥R)) : DihedralGroup n)⁻¹ from by
          simp]
    exact h2
  obtain ⟨phi, phi_r, phi_sr⟩ := DihHelp.dih_lift_of_cyclic_rot g sH hgmul hsH2 hSc
  have hinj : Function.Injective phi := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    cases x with
    | r i =>
      have hg : g i = 1 := by rw [← phi_r i]; exact hx
      have h1 : (e (Multiplicative.ofAdd i) : ↥R) = 1 := by
        apply Subtype.ext
        exact congrArg (fun z : ↥H => (z : DihedralGroup n)) hg
      have h2 : (Multiplicative.ofAdd i : Multiplicative (ZMod m)) = 1 :=
        e.injective (by rw [h1, map_one])
      have h3 : i = 0 := Multiplicative.ofAdd.injective (by simpa using h2)
      rw [h3, DihedralGroup.r_zero]
    | sr i =>
      exfalso
      have hg : sH * g i = 1 := by rw [← phi_sr i]; exact hx
      have h1 : (sr u : DihedralGroup n) = (((e (Multiplicative.ofAdd i))⁻¹ : ↥R) :
          DihedralGroup n) := by
        have h := congrArg (fun z : ↥H => (z : DihedralGroup n)) hg
        simp only [Subgroup.coe_mul, Subgroup.coe_one, hsHval, hgval i] at h
        simpa [Subgroup.coe_inv] using eq_inv_of_mul_eq_one_left h
      exact hsu (by rw [h1]; exact hRrot ((e (Multiplicative.ofAdd i))⁻¹).2)
  have hsurj : Function.Surjective phi := by
    intro y
    rcases DihHelp.dih_decomp_reflection hsH y.2 with ⟨k, hk⟩ | ⟨k, hk, hkH⟩
    · have hyR : ((y : ↥H) : DihedralGroup n) ∈ H ⊓ Work.Dihedral.rot n :=
        ⟨y.2, by rw [hk]; exact Work.Dihedral.r_mem_rot k⟩
      obtain ⟨w, hw⟩ := e.surjective ⟨((y : ↥H) : DihedralGroup n), hyR⟩
      refine ⟨DihedralGroup.r (Multiplicative.toAdd w), ?_⟩
      rw [phi_r]
      apply Subtype.ext
      show ((e (Multiplicative.ofAdd (Multiplicative.toAdd w)) : ↥R) : DihedralGroup n)
        = ((y : ↥H) : DihedralGroup n)
      rw [show Multiplicative.ofAdd (Multiplicative.toAdd w) = w from by simp, hw]
    · have hkR : (DihedralGroup.r k : DihedralGroup n) ∈ H ⊓ Work.Dihedral.rot n :=
        ⟨hkH, Work.Dihedral.r_mem_rot k⟩
      obtain ⟨w, hw⟩ := e.surjective ⟨(DihedralGroup.r k : DihedralGroup n), hkR⟩
      have hy : y = (⟨DihedralGroup.r k, hkH⟩ : ↥H) * sH := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, hsHval]
        exact hk
      have hgz : (⟨DihedralGroup.r k, hkH⟩ : ↥H) = g (Multiplicative.toAdd w) := by
        apply Subtype.ext
        show (DihedralGroup.r k : DihedralGroup n)
          = ((e (Multiplicative.ofAdd (Multiplicative.toAdd w)) : ↥R) : DihedralGroup n)
        rw [show Multiplicative.ofAdd (Multiplicative.toAdd w) = w from by simp, hw]
      refine ⟨DihedralGroup.sr (- Multiplicative.toAdd w), ?_⟩
      rw [phi_sr, hy, hgz]
      exact (hSc (Multiplicative.toAdd w)).symm
  exact ⟨m, ⟨(MulEquiv.ofBijective phi ⟨hinj, hsurj⟩).symm⟩⟩

end

/-- Every subgroup of `DihedralGroup n` is cyclic or dihedral (the case `n = 0`, the infinite dihedral group, included).  Raw group-theoretic input of the DSTR leaves `DS1` and `DS6`. -/
theorem dihedralSubgroup : Work.GW2.DihedralSubgroupProp := by
  intro n H
  by_cases hle : H ≤ Work.Dihedral.rot n
  · left
    exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  · right
    obtain ⟨s, hsH, hs⟩ := Set.not_subset.mp hle
    obtain ⟨u, hsu⟩ : ∃ u : ZMod n, s = sr u := (Work.Dihedral.notMem_rot).mp hs
    subst hsu
    exact dihedral_case n H u hsH hs

end Work.DSTR
