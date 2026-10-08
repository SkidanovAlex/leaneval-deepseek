import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Elementary
import Submission.Work.AUTL2.A5.kleinExtend
import Submission.Work.AUTL2.Norm.fourgroup
import Submission.Work.AUTL2.Helper.not_elementaryAbelian_card_eight_of_dihOrCycSylow

namespace Work.AUTL2.Helper

theorem not_dihOrCycSylow_of_mem_galHom (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    [DecidableEq (GaloisField p k)] (hp : Odd p) (hq : 5 ≤ p ^ k)
    (Q : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hpsl : Work.AUTL2.pslImage (GaloisField p k) ≤ Q)
    (σ : GaloisField p k ≃+* GaloisField p k) (hσ : σ * σ = 1) (hne : σ ≠ 1)
    (hmem : Work.AUTL2.galHom (GaloisField p k) σ ∈ Q) :
    ¬ Work.GW2.DihOrCycSylow ↥Q := by
  classical
  intro hdih
  -- A Klein four-group `V ≤ pslImage ≤ Q` centralizing the involution `galHom σ`.
  obtain ⟨V, hVcard, hVpsl, hVsq, hVcomm⟩ := Work.AUTL2.Norm.fourgroup p k hp hq σ hσ hne
  have hVQ : V ≤ Q := hVpsl.trans hpsl
  -- `galHom σ` is an involution, and it is not in `pslImage`.
  have hτ2 : Work.AUTL2.galHom (GaloisField p k) σ * Work.AUTL2.galHom (GaloisField p k) σ = 1 := by
    rw [← map_mul, hσ, map_one]
  have hτ1 : Work.AUTL2.galHom (GaloisField p k) σ ≠ 1 := by
    intro h
    exact hne (Work.AUTL2.Galois.galHom_injective (GaloisField p k) (by rw [h, map_one]))
  have hτV : Work.AUTL2.galHom (GaloisField p k) σ ∉ V := by
    intro hmemV
    have h1 : Work.AUTL2.galHom (GaloisField p k) σ ∈
        Work.AUTL2.pglImage (GaloisField p k) ⊓ Work.AUTL2.galSub (GaloisField p k) :=
      ⟨Work.AUTL2.pslImage_le_pglImage (GaloisField p k) (hVpsl hmemV), ⟨σ, rfl⟩⟩
    rw [Work.AUTL2.Galois.pglImage_inf_galSub] at h1
    exact hτ1 h1
  -- Work inside `Q`.
  let τ' : ↥Q := ⟨Work.AUTL2.galHom (GaloisField p k) σ, hmem⟩
  let V' : Subgroup ↥Q := V.subgroupOf Q
  have hV'card : Nat.card V' = 4 := by
    have h := Subgroup.card_map_of_injective (K := V') (f := Q.subtype)
      (Subgroup.subtype_injective Q)
    rw [Subgroup.map_subgroupOf_eq_of_le hVQ] at h
    exact h.symm.trans hVcard
  have hV'sq : ∀ v ∈ V', v * v = 1 := by
    intro v hv
    refine Subtype.ext ?_
    have hvV : (v : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) ∈ V :=
      Subgroup.mem_subgroupOf.mp hv
    have := hVsq (v : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) hvV
    simpa [pow_two] using this
  have hτ'2 : τ' * τ' = 1 := Subtype.ext hτ2
  have hτ'V' : τ' ∉ V' := by
    intro hmem'
    exact hτV (Subgroup.mem_subgroupOf.mp hmem')
  have hcomm' : ∀ v ∈ V', v * τ' = τ' * v := by
    intro v hv
    refine Subtype.ext ?_
    exact (hVcomm (v : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))
      (Subgroup.mem_subgroupOf.mp hv)).symm
  -- `V'` extends to an elementary abelian subgroup of order `8` inside `Q`.
  obtain ⟨E, hEcard, _, _, hEsq⟩ :=
    Work.AUTL2.A5.kleinExtend V' τ' hV'card hV'sq hτ'2 hτ'V' hcomm'
  exact not_elementaryAbelian_card_eight_of_dihOrCycSylow hdih ⟨E, hEcard, hEsq⟩

end Work.AUTL2.Helper
