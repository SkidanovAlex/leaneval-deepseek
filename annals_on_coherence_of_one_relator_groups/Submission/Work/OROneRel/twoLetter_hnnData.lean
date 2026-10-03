/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The `Z`-domain (Magnus--Moldavanskii) step for the two-letter relator `a ^ p * b ^ q`

Target (`Work.OROneRel.twoLetter_hnnData`): for coprime `p q ≥ 1` and `l ≥ 1`, the one-relator group
`G = ⟨x0, x1, x2 | x2 ^ l, x1 ^ q * x2⁻¹ * x0 ^ p⟩` -- which is the two-letter group
`⟨a, b | (a ^ p * b ^ q) ^ l⟩` in the Tietze presentation of `twoLetter_amalgam_tietze` -- is an HNN
extension of a one-relator group `⟨β | v ^ l⟩` with `v` not a proper power,
`relatorNorm v < p + q`, and the class of the Tietze generator `x2` conjugate to the class of `v`.

## The proof, in three steps

1. **Reduction to the `Z`-domain datum.**  `twoLetter_hnnData_of_datum` shows that the target follows
   from `MagnusDomainDatum (tlU p q) l`: `magnus_step_root_no_eps_zero_of_domainDatum` turns the datum
   into the target for the two-letter presentation `⟨a, b | (a ^ p * b ^ q) ^ l⟩`, and the Tietze
   isomorphism `twoLetter_amalgam_tietze` (which carries the class of `a ^ p * b ^ q` to the class of
   the generator `x2`) transports it to the target's presentation.

2. **The band window data and the generation plank.**  `twoLetterWindowData_tlW` supplies the window
   `[0, p * q]` of the weight `tlW p q` (with `tlW p q a = q`, `tlW p q b = -p`) with its tree-path
   gauge `Wt`, the norm decrease `winRootNormLt`, the aperiodicity of the deleted walk word, and the
   *Freiheitssatz* `twoLetterFreiheitssatz` of the domain -- i.e. the identification of the window
   vertex `winVertex Wt (tlW p q) 0 (p * q) (tlU p q) l` (the fundamental group of the band domain
   `D = [0, p * q]`) with the one-relator group
   `⟨winBeta Wt (tlW p q) 0 (p * q) | winRoot ^ l⟩`.  `twoLetter_generation` is the generation plank
   `winVertex ⊔ ⟨mk tlLowTau⟩ = ⊤` of the splitting.

3. **The splitting.**  `twoLetter_hnnConjMap_injective` is Linton's graph-of-spaces splitting for the
   *line* of band domains (*One-relator hierarchies*, arXiv 2202.11324, Proposition 4.3 with 2.2.19),
   in its sharp pin-free form: the canonical comparison map
   `hnnConjMap ↥(winVertex) (mk tlLowTau)` -- whose associated subgroups are the *gates*
   `winVertex ⊓ τ^{∓1}(winVertex)τ^{±1}` of the band, *not* the whole vertex, which is why the
   "pin" `mk (Wt i) * (mk τ)^{-i} ∈ hnnEdgeA ...` is false for a general gauge -- is injective.
   Together with the generation plank it is an isomorphism, and `magnusDomainDatum_of_bandInjective`
   (proved here) carries its inverse to the `Z`-domain datum, whence the target by step 1.

Two independent routes to the datum are recorded elsewhere in the workspace and were used in earlier
versions of this file: for `l = 1` with `2 ≤ p, q` the weight kernel of the torus-knot group is free
(`magnusStepDataOne_cpRelator_general`, via `magnusDomainDatum_of_kernelData` with `A = B = ⊤`), and
for `p = 1` or `q = 1` the relator has a generator occurring once, so that
`⟨a, b | (a b ^ q) ^ l⟩ ≅ ℤ/l ∗ ℤ` is an HNN extension with both associated subgroups trivial
(`twoLetter_tlU_one_hnnIso`, `twoLetter_tlU_one_right_hnnIso`).
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.wordOfDefs
import Submission.Work.OROneRel.twoLetter_amalgam_tietze
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winRho_winRoot
import Submission.Work.OROneRel.winRootNormLt
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.magnus_step_root_no_eps_zero
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.twoLetterWindowData_tlW
import Submission.Work.OROneRel.twoLetter_generation
import Submission.Work.OROneRel.hnnConjSplit
import Submission.Work.OROneRel.twoLetter_hnnConjMap_injective

namespace Work.OROneRel

/-! ## The target's conclusion from a `MagnusDomainDatum` of the two-letter relator -/

/-- **The target's conclusion from a `MagnusDomainDatum` of the two-letter relator.**  The Tietze
isomorphism `twoLetter_amalgam_tietze` carries the class of `a ^ p * b ^ q` to the Tietze generator
`x2`, so the Magnus step for the two-letter presentation transports to the target's presentation. -/
theorem twoLetter_hnnData_of_datum {p q l : ℕ}
    (D : MagnusDomainDatum (tlU p q) l) :
    ∃ (β : Type) (v : FreeGroup β)
      (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β))))
      (φ : A ≃* B)
      (e : PresentedGroup ({FreeGroup.of (2 : Fin 3) ^ l,
          FreeGroup.of (1 : Fin 3) ^ q * (FreeGroup.of (2 : Fin 3))⁻¹ *
            FreeGroup.of (0 : Fin 3) ^ p} : Set (FreeGroup (Fin 3))) ≃*
        HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
      ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v <
        Work.OROneRel.relatorNorm (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) ∧
      ∃ c' : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
        e (PresentedGroup.mk _ (FreeGroup.of (2 : Fin 3))) =
          c' * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c'⁻¹ := by
  classical
  -- the Magnus step for the two-letter presentation `⟨a, b | (a ^ p * b ^ q) ^ l⟩`
  obtain ⟨β, v, hpp, hnorm, A, B, φ, e, c, hc⟩ :=
    magnus_step_root_no_eps_zero_of_domainDatum (tlU p q) l D
  -- transport along the Tietze isomorphism of `twoLetter_amalgam_tietze`
  obtain ⟨eT, heT⟩ := twoLetter_amalgam_tietze p q l
  refine ⟨β, v, A, B, φ, eT.symm.trans e, hpp, ?_, c, ?_⟩
  · simpa only [tlU] using hnorm
  · show e (eT.symm (PresentedGroup.mk _ (FreeGroup.of (2 : Fin 3)))) = _
    have h1 : eT.symm (PresentedGroup.mk _ (FreeGroup.of (2 : Fin 3))) =
        PresentedGroup.mk _ (tlU p q) := by
      apply eT.injective
      rw [MulEquiv.apply_symm_apply]
      simpa only [tlU] using heT.symm
    rw [h1]
    exact hc

/-! ## The assembly of the `Z`-domain datum from the injectivity of the comparison map -/

/-- **The `Z`-domain datum from the injectivity of the canonical comparison map.**  The band window
data of `twoLetterWindowData_tlW` (the tree-path gauge `hW0`/`hcoh`, the walk in the window `hwin`,
the strictly deleted traversal `hone`, and the Freiheitssatz of the domain `hFrei`) together with the
injectivity of `hnnConjMap ↥(winVertex) τG` -- Linton's graph-of-spaces splitting for the line of
band domains -- produce the `Z`-domain datum of `tlU p q`.

The comparison map is an isomorphism by the *proved* generation plank `twoLetter_generation`, and the
HNN structure over the vertex is transported along its inverse; nothing else is needed.  The
associated subgroups of the resulting splitting are the *maximal* ones
`hnnEdgeA (winVertex) τG`, `hnnEdgeB (winVertex) τG`, i.e.
`winVertex ⊓ τG^{∓1}(winVertex)τG^{±1}`. -/
noncomputable def magnusDomainDatum_of_bandInjective (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hl : 1 ≤ l) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, cohom (tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (hone : ∃ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winTree Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (hFrei : ∀ x : FreeGroup (winBeta Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ))),
      winRho Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) x ∈
          Subgroup.normalClosure ({tlU p q ^ l} : Set (FreeGroup (Fin 2))) →
        x ∈ Subgroup.normalClosure
          ({winRoot Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q) ^ l} :
            Set (FreeGroup (winBeta Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ))))))
    (hinj : Function.Injective (hnnConjMap
      (winVertex Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q) l)
      (PresentedGroup.mk ({tlU p q ^ l} : Set (FreeGroup (Fin 2))) (tlLowTau p q hp hq hcop)))) :
    MagnusDomainDatum (tlU p q) l := by
  classical
  let τG : PresentedGroup ({tlU p q ^ l} : Set (FreeGroup (Fin 2))) :=
    PresentedGroup.mk ({tlU p q ^ l} : Set (FreeGroup (Fin 2))) (tlLowTau p q hp hq hcop)
  let H : Subgroup (PresentedGroup ({tlU p q ^ l} : Set (FreeGroup (Fin 2)))) :=
    winVertex Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q) l
  have hcu : cohom (tlW p q) (tlU p q) = 1 := cohom_tlW_tlU_local p q
  have hτ : cohom (tlW p q) (tlLowTau p q hp hq hcop) = Multiplicative.ofAdd 1 :=
    tlLowTau_cohom p q hp hq hcop
  -- the generation plank, and hence the isomorphism
  have hgen : H ⊔ Subgroup.closure {τG} = ⊤ :=
    twoLetter_generation p q l hp hq hl hcop hW0 hcoh hwin
  have hbij : Function.Bijective (hnnConjMap H τG) := hnnConjMap_bijective H τG hinj hgen
  have he_of : ∀ h : ↥H, (MulEquiv.ofBijective (hnnConjMap H τG) hbij) (HNNExtension.of h) =
      (h : PresentedGroup ({tlU p q ^ l} : Set (FreeGroup (Fin 2)))) := by
    intro h
    show hnnConjMap H τG (HNNExtension.of h) = _
    rw [hnnConjMap_of]
  have he_t : (MulEquiv.ofBijective (hnnConjMap H τG) hbij) HNNExtension.t = τG := by
    show hnnConjMap H τG HNNExtension.t = _
    rw [hnnConjMap_t]
  -- the deleted walk word is not a proper power
  have hppv : ¬ IsProperPower (winRoot Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q)) := by
    rintro ⟨z, k, hk, hz⟩
    refine tlU_not_isProperPower p q hp hq
      ⟨winRho Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) z, k, hk, ?_⟩
    have h2 : winRho Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ))
        (winRoot Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q)) =
        winRho Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) z ^ k := by
      rw [hz, map_pow]
    rwa [winRho_winRoot Wt hW0 hcu 0 ((p : ℤ) * (q : ℤ)) hwin] at h2
  -- the norm bound
  have hnorm : relatorNorm (winRoot Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q)) <
      relatorNorm (tlU p q) :=
    winRootNormLt Wt 0 ((p : ℤ) * (q : ℤ)) (tlU_isCyclicallyReduced p q hp hq) hwin hone
  exact magnusDomainDatum_of_winData (tlU p q) l hcu Wt 0 ((p : ℤ) * (q : ℤ))
    (tlLowTau p q hp hq hcop) hW0 hwin hτ hppv hnorm hFrei
    ((hnnEdgeA H τG).subgroupOf H) ((hnnEdgeB H τG).subgroupOf H) (hnnConjEquiv H τG)
    (MulEquiv.ofBijective (hnnConjMap H τG) hbij) he_of he_t

/-! ## The target -/

theorem twoLetter_hnnData (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hl : 1 ≤ l) (hcop : Nat.Coprime p q) :
    ∃ (β : Type) (v : FreeGroup β)
      (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β))))
      (φ : A ≃* B)
      (e : PresentedGroup ({FreeGroup.of (2 : Fin 3) ^ l,
          FreeGroup.of (1 : Fin 3) ^ q * (FreeGroup.of (2 : Fin 3))⁻¹ *
            FreeGroup.of (0 : Fin 3) ^ p} : Set (FreeGroup (Fin 3))) ≃*
        HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
      ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v <
        Work.OROneRel.relatorNorm (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) ∧
      ∃ c' : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
        e (PresentedGroup.mk _ (FreeGroup.of (2 : Fin 3))) =
          c' * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c'⁻¹ := by
  classical
  -- the band window data of `twoLetterWindowData_tlW`: the window `[0, p * q]` of the weight
  -- `tlW p q`, its tree-path gauge, the Freiheitssatz of the domain, and a strictly deleted
  -- traversal of the walk of `tlU p q`
  obtain ⟨Wt, hW0, hcoh, hwin, _htight, htree, hone, hFrei⟩ :=
    twoLetterWindowData_tlW p q l hp hq hl hcop
  -- the generation plank of the window splitting
  have hgen : winVertex Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q) l ⊔
      Subgroup.closure (singleton (PresentedGroup.mk ({tlU p q ^ l} : Set (FreeGroup (Fin 2)))
        (tlLowTau p q hp hq hcop))) = ⊤ :=
    twoLetter_generation p q l hp hq hl hcop hW0 hcoh hwin
  -- the `Z`-domain datum from the injectivity of the comparison map (Linton's splitting of the
  -- band), and the target from the datum
  exact twoLetter_hnnData_of_datum
    (magnusDomainDatum_of_bandInjective p q l hp hq hl hcop Wt hW0 hcoh hwin hone hFrei
      (twoLetter_hnnConjMap_injective p q l hp hq hl hcop Wt hW0 hcoh hwin htree hFrei hgen))

end Work.OROneRel
