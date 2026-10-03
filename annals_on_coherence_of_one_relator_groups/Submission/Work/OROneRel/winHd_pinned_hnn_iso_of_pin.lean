import Mathlib
import Submission.Work.OROneRel.hnnSplitPin
import Submission.Work.OROneRel.hnnSplitAssembly
import Submission.Work.OROneRel.winPinResidual
import Submission.Work.OROneRel.twoMapsDefs
import Submission.Work.OROneRel.hnnExtension_iso_of_baseMulEquiv

namespace Work.OROneRel

universe u

theorem winHd_pinned_hnn_iso_of_pin {α : Type u} [Fintype α] [DecidableEq α]
    (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    {c : α → ℤ} (hcu : Work.OROneRel.cohom c u = 1)
    {Wt : ℤ → FreeGroup α} {lo hi : ℤ} (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (hlo1 : lo ≤ 1) (hhi1 : 1 ≤ hi)
    (hθ : Function.Injective (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin))
    {A : Subgroup (Work.OROneRel.winHd Wt c lo hi u l)} {ψ : A ≃* A}
    (hψ : ∀ a : A, PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1) *
        Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin
          (a : Work.OROneRel.winHd Wt c lo hi u l) =
      Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin
          (ψ a : Work.OROneRel.winHd Wt c lo hi u l) *
        PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1))
    {Q : ℤ → Work.OROneRel.winHd Wt c lo hi u l}
    (hQ : ∀ j : ℤ, Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin (Q j) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt j * (Wt 1) ^ (-j)))
    (hcons : ∀ (x : α) (i j : ℤ), (x, i) ∈ Work.OROneRel.winE c lo hi →
      (x, j) ∈ Work.OROneRel.winE c lo hi →
      (Work.OROneRel.levelEl (A := A) (ψ := ψ) Q i)⁻¹ *
          Work.OROneRel.winGammaK Wt c lo hi u l A ψ (x, i) *
          Work.OROneRel.levelEl (A := A) (ψ := ψ) Q (i + c x) =
        (Work.OROneRel.levelEl (A := A) (ψ := ψ) Q j)⁻¹ *
          Work.OROneRel.winGammaK Wt c lo hi u l A ψ (x, j) *
          Work.OROneRel.levelEl (A := A) (ψ := ψ) Q (j + c x)) :
    ∃ (A' B' : Subgroup ↥(Work.OROneRel.winVertex Wt c lo hi u l)) (φ' : A' ≃* B')
      (e : HNNExtension ↥(Work.OROneRel.winVertex Wt c lo hi u l) A' B' φ' ≃*
        PresentedGroup ({u ^ l} : Set (FreeGroup α))),
      (∀ h : ↥(Work.OROneRel.winVertex Wt c lo hi u l),
        e (HNNExtension.of h) = (h : PresentedGroup ({u ^ l} : Set (FreeGroup α)))) ∧
      e HNNExtension.t = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1) := by
  classical
  -- the pin at the levels `0` and `1`
  have hQ0 : Q 0 = 1 := by
    apply hθ
    have h1 : Wt 0 * (Wt 1) ^ (-(0 : ℤ)) = 1 := by
      rw [hW0, one_mul]
      exact zpow_zero (Wt 1)
    rw [hQ 0, map_one, h1, map_one]
  have hQ1 : Q 1 = 1 := by
    apply hθ
    have h1 : Wt 1 * (Wt 1) ^ (-(1 : ℤ)) = 1 := by
      rw [zpow_neg_one, mul_inv_cancel]
    rw [hQ 1, map_one, h1, map_one]
  -- the level factors lie in the vertex
  have hpin : ∀ i : ℤ, PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt i) *
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1)) ^ (-i) ∈
      Work.OROneRel.winVertex Wt c lo hi u l := by
    intro i
    have h := hQ i
    rw [map_mul, map_zpow] at h
    rw [← h,
      show Work.OROneRel.winVertex Wt c lo hi u l =
          (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin).range from
        (Work.OROneRel.winTheta_range Wt c lo hi u l hW0 hcu hwin).symm]
    exact ⟨Q i, rfl⟩
  -- generation of the whole group by the vertex and the deck element
  have hgen : (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin).range ⊔
      Subgroup.zpowers (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1)) = ⊤ := by
    rw [Work.OROneRel.winTheta_range Wt c lo hi u l hW0 hcu hwin, Subgroup.zpowers_eq_closure]
    exact Work.OROneRel.winVertex_generation_of_pin u l hl c (Wt 1) Wt lo hi hcu hcov hpin
  -- the generator image of the two-maps construction and its three conditions
  have hXu : FreeGroup.lift (Work.OROneRel.genX (A := A) (ψ := ψ) hcov Q) (u ^ l) = 1 :=
    Work.OROneRel.lift_genX_pow (A := A) (ψ := ψ) hcu hwin hcov Q hQ0 hcons
  have hXτ : FreeGroup.lift (Work.OROneRel.genX (A := A) (ψ := ψ) hcov Q) (Wt 1) =
      HNNExtension.t :=
    Work.OROneRel.lift_genX_Wt_one (A := A) (ψ := ψ) hcov Q hQ0 hQ1 hcons hcoh htree hlo1 hhi1
  have hXβ : ∀ e : Work.OROneRel.winBeta Wt c lo hi,
      FreeGroup.lift (Work.OROneRel.genX (A := A) (ψ := ψ) hcov Q)
        (Work.OROneRel.coverClassAt Wt c e.1) = HNNExtension.of (PresentedGroup.of e) :=
    fun e => Work.OROneRel.lift_genX_coverClassAt (A := A) (ψ := ψ) hcov Q hQ0 hcons hcoh htree e
  -- the explicit inverse `Φ` of the comparison map
  have hXu' : ∀ r ∈ ({u ^ l} : Set (FreeGroup α)),
      FreeGroup.lift (Work.OROneRel.genX (A := A) (ψ := ψ) hcov Q) r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact hXu
  set Φ : PresentedGroup ({u ^ l} : Set (FreeGroup α)) →* Work.OROneRel.winK A ψ :=
    PresentedGroup.toGroup (f := Work.OROneRel.genX (A := A) (ψ := ψ) hcov Q) hXu' with hΦ
  have hΦ_mk : ∀ w : FreeGroup α,
      Φ (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) w) =
        FreeGroup.lift (Work.OROneRel.genX (A := A) (ψ := ψ) hcov Q) w := fun _ => rfl
  have hΦ_of : ∀ h : Work.OROneRel.winHd Wt c lo hi u l,
      Φ (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin h) = HNNExtension.of h := by
    have key : Φ.comp (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin) =
        HNNExtension.of := by
      refine PresentedGroup.ext (fun e => ?_)
      rw [MonoidHom.comp_apply, Work.OROneRel.winTheta_of, hΦ_mk, hXβ e]
    intro h
    exact congrArg (fun f : Work.OROneRel.winHd Wt c lo hi u l →* Work.OROneRel.winK A ψ => f h)
      key
  -- the pinned isomorphism `PresentedGroup ≃* HNNExtension winHd A A ψ`
  obtain ⟨e0, he_of, he_t⟩ := Work.OROneRel.hnnExtension_iso_of_explicit_inverse A ψ
    (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin)
    (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1)) hψ hgen Φ hΦ_of
    (by rw [hΦ_mk]; exact hXτ)
  -- the vertex presentations are identified by `winTheta`
  have hrange : (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin).range =
      Work.OROneRel.winVertex Wt c lo hi u l :=
    Work.OROneRel.winTheta_range Wt c lo hi u l hW0 hcu hwin
  let iso : Work.OROneRel.winHd Wt c lo hi u l ≃*
      ↥(Work.OROneRel.winVertex Wt c lo hi u l) :=
    (MonoidHom.ofInjective hθ).trans (MulEquiv.subgroupCongr hrange)
  have hiso : ∀ h : Work.OROneRel.winHd Wt c lo hi u l,
      ((iso h : ↥(Work.OROneRel.winVertex Wt c lo hi u l)) :
          PresentedGroup ({u ^ l} : Set (FreeGroup α))) =
        Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin h := fun _ => rfl
  obtain ⟨A', B', φ', E, -, -, hE_of, hE_t⟩ :=
    Work.OROneRel.hnnExtension_iso_of_baseMulEquiv iso A A ψ
  refine ⟨A', B', φ', E.symm.trans e0.symm, ?_, ?_⟩
  · intro h
    have h1 : E.symm (HNNExtension.of h) = HNNExtension.of (iso.symm h) := by
      rw [MulEquiv.symm_apply_eq, hE_of (iso.symm h), MulEquiv.apply_symm_apply]
    have h3 : Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin (iso.symm h) =
        (h : PresentedGroup ({u ^ l} : Set (FreeGroup α))) := by
      rw [← hiso (iso.symm h), MulEquiv.apply_symm_apply]
    rw [MulEquiv.trans_apply, h1, ← he_of (iso.symm h), MulEquiv.symm_apply_apply, h3]
  · have h1 : E.symm HNNExtension.t = HNNExtension.t := by
      rw [MulEquiv.symm_apply_eq]
      exact hE_t.symm
    rw [MulEquiv.trans_apply, h1, ← he_t, MulEquiv.symm_apply_apply]

end Work.OROneRel
