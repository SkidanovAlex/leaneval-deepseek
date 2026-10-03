import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.twoLetter_hnnData
import Submission.Work.OROneRel.twoLetter_amalgam_tietze

namespace Work.OROneRel

theorem twoLetter_magnusData (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hl : 1 ≤ l)
    (hcop : Nat.Coprime p q) :
    ∃ (β : Type) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v <
        Work.OROneRel.relatorNorm (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup
            ({(FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) ^ l} :
              Set (FreeGroup (Fin 2))) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk
              ({(FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) ^ l} :
                Set (FreeGroup (Fin 2)))
              (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q)) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  -- The band window data of `twoLetterWindowData_tlW`.
  obtain ⟨Wt, hW0, hcoh, hwin, _htight, htree, hone, hFrei⟩ :=
    twoLetterWindowData_tlW p q l hp hq hl hcop
  -- The generation plank of the window splitting.
  have hgen : winVertex Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q) l ⊔
      Subgroup.closure (singleton (PresentedGroup.mk ({tlU p q ^ l} : Set (FreeGroup (Fin 2)))
        (tlLowTau p q hp hq hcop))) = ⊤ :=
    twoLetter_generation p q l hp hq hl hcop hW0 hcoh hwin
  -- The target is the conclusion of the `Z`-domain step applied to the datum built from Linton's
  -- splitting of the band (`twoLetter_hnnConjMap_injective`).
  refine magnus_step_root_no_eps_zero_of_domainDatum (tlU p q) l ?_
  exact magnusDomainDatum_of_bandInjective p q l hp hq hl hcop Wt hW0 hcoh hwin hone hFrei
    (twoLetter_hnnConjMap_injective p q l hp hq hl hcop Wt hW0 hcoh hwin htree hFrei hgen)

end Work.OROneRel
