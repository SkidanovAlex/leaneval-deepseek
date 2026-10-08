import Mathlib
import Submission.Work.ZJB2.Defs

namespace Work.ZJB2

/-- Glauberman 1968, Lemma 5.2 (pointwise form).  Let `N = O_{p'}(H)`, `P = O_{p',p}(H)` the
preimage of `O_p(H/N)`, and `S ∈ Syl_p(H)`.  If `C_H(S ∩ P) ∩ S ≤ S ∩ P` then every element of
`H/N` that lies both in `C_{H/N}(O_p(H/N))` and in the image `SN/N` of `S` already lies in
`O_p(H/N)`.

Proof: pick `s ∈ S` with `π(s) = x`.  For `a ∈ S ∩ P` the element `π(a)` lies in `O_p(H/N)`, so
the centrality of `x` gives `s a s⁻¹ a⁻¹ ∈ N`.  On the other hand `s a s⁻¹ a⁻¹ ∈ S ∩ P` because
`P ⊴ H` and `S ∩ P ⊴ S`.  But `N` is a `p'`-group while `S ∩ P` is a `p`-group, so they intersect
trivially; hence `s a s⁻¹ a⁻¹ = 1`, i.e. `s` centralises `S ∩ P`, and the hypothesis gives
`s ∈ S ∩ P ≤ P`, whence `x = π(s) ∈ O_p(H/N)`. -/
theorem l52MemPCore (p : ℕ) [Fact p.Prime] (H : Type) [Group H] [Finite H] (S : Sylow p H)
    (hhyp : Subgroup.centralizer (((S : Subgroup H) ⊓ Work.ZJB.OppCore p H : Subgroup H) : Set H)
        ⊓ (S : Subgroup H) ≤ (S : Subgroup H) ⊓ Work.ZJB.OppCore p H)
    {x : H ⧸ Work.ZJB.OpPrime p H}
    (hx1 : x ∈ Subgroup.centralizer ((Work.GW2.pCore p (H ⧸ Work.ZJB.OpPrime p H)) :
        Set (H ⧸ Work.ZJB.OpPrime p H)))
    (hx2 : x ∈ (S : Subgroup H).map (QuotientGroup.mk' (Work.ZJB.OpPrime p H))) :
    x ∈ Work.GW2.pCore p (H ⧸ Work.ZJB.OpPrime p H) := by
  -- `x` is the image of an element `s` of the Sylow subgroup `S`.
  obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hx2
  -- `S ∩ P` is a `{p}`-subgroup and `N = O_{p'}(H)` a `{p}ᶜ`-subgroup, so they are disjoint.
  have hP1pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)
      ((S : Subgroup H) ⊓ Work.ZJB.OppCore p H) :=
    Subgroup.isPiSubgroup_of_isPGroup_of_mem
      (IsPGroup.to_le S.isPGroup' inf_le_left) rfl
  have hNpi : Subgroup.IsPiSubgroup (({p} : Set ℕ)ᶜ) (Work.ZJB.OpPrime p H) := by
    have h := OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (({p} : Set ℕ)ᶜ) (G := H)
    rw [← Work.GW2.piCore_eq_oPiCore] at h
    exact h
  have hbot : ((S : Subgroup H) ⊓ Work.ZJB.OppCore p H) ⊓ Work.ZJB.OpPrime p H = ⊥ :=
    OddOrder.GroupTheory.inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl hP1pi hNpi
  have hPnorm : (Work.ZJB.OppCore p H).Normal := by
    unfold Work.ZJB.OppCore
    infer_instance
  -- `s` centralises `S ∩ P`.
  have hcen : s ∈ Subgroup.centralizer
      (((S : Subgroup H) ⊓ Work.ZJB.OppCore p H : Subgroup H) : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : a ∈ (S : Subgroup H) ⊓ Work.ZJB.OppCore p H := ha
    obtain ⟨haS, haP⟩ := Subgroup.mem_inf.mp ha'
    -- `π(a) ∈ O_p(H/N)` and `x = π(s)` centralises it.
    have haQ : QuotientGroup.mk' (Work.ZJB.OpPrime p H) a ∈
        Work.GW2.pCore p (H ⧸ Work.ZJB.OpPrime p H) := haP
    have hcomm : ((a : H ⧸ Work.ZJB.OpPrime p H)) * ((s : H ⧸ Work.ZJB.OpPrime p H)) =
        ((s : H ⧸ Work.ZJB.OpPrime p H)) * ((a : H ⧸ Work.ZJB.OpPrime p H)) :=
      (Subgroup.mem_centralizer_iff.mp hx1) _ haQ
    -- hence `s a s⁻¹ a⁻¹ ∈ N` ...
    have hNmem : (s * a) * (a * s)⁻¹ ∈ Work.ZJB.OpPrime p H := by
      rw [← QuotientGroup.eq_one_iff ((s * a) * (a * s)⁻¹)]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hcomm]
      simp
    -- ... while `s a s⁻¹ a⁻¹ ∈ S ∩ P` (`P ⊴ H` and `S ∩ P ⊴ S`).
    have hconj : s * a * s⁻¹ ∈ Work.ZJB.OppCore p H := hPnorm.conj_mem a haP s
    have hPmem : (s * a) * (a * s)⁻¹ ∈ (S : Subgroup H) ⊓ Work.ZJB.OppCore p H := by
      have heq : (s * a) * (a * s)⁻¹ = (s * a * s⁻¹) * a⁻¹ := by group
      rw [heq]
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hsS haS)
              (Subgroup.inv_mem _ hsS)) (Subgroup.inv_mem _ haS),
             Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ haP)⟩
    -- The two intersections are trivial, so `s a s⁻¹ a⁻¹ = 1`.
    have hone : (s * a) * (a * s)⁻¹ = 1 := by
      have hmem : (s * a) * (a * s)⁻¹ ∈ (⊥ : Subgroup H) := by
        rw [← hbot]
        exact ⟨hPmem, hNmem⟩
      simpa using hmem
    exact (mul_inv_eq_one.mp hone).symm
  -- The hypothesis now places `s` in `S ∩ O_{p',p}(H)`, i.e. `x` in `O_p(H/N)`.
  have hsP : s ∈ (S : Subgroup H) ⊓ Work.ZJB.OppCore p H := hhyp ⟨hcen, hsS⟩
  exact hsP.2

end Work.ZJB2
