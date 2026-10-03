import Mathlib
import Submission.Work.OROneRel.hnnSplitPin
import Submission.Work.OROneRel.winGammaWord_prod_eq_mk

/-!
# The relation condition of the two-maps construction

The last of the three conditions of the two-maps construction
(`Submission/Work/OROneRel/hnnSplitAssembly.lean`): the generator image `X` built from the pin kills
the relator `u ^ l`.

The telescoping identity `Work.OROneRel.walking_telescope` along the walk of a word `w` gives

  `V 0 * (the product of the `X`-images of the letters of `w`)
     = (the coedge product over the walk of `w`) * V (lsig c (wordOf w))`,

the coedge product is the image in the HNN of the `β`-word spelled by the filtered walk
(`Work.OROneRel.winGammaWord_prod_eq_mk`), and `lsig c (wordOf w) = 0` when `cohom c w = 1`.  Hence

  `FreeGroup.lift X w = of (mk (the filtered walk word))`.

For `w = u` the filtered walk word is `winRoot` (`winRoot_eq`), whose `l`-th power is the relator
of the vertex, so `FreeGroup.lift X (u ^ l) = 1`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The relation condition of the two-maps construction, in the form of a general word.**  The
telescoping along the walk of `w` computes the value of the comparison map on `w` as the class of the
filtered walk word. -/
theorem lift_genX_word {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α} {l : ℕ}
    {A : Subgroup (winHd Wt c lo hi u l)} {ψ : A ≃* A} {w : FreeGroup α}
    (hcu : Work.OROneRel.cohom c w = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf w),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (Q : ℤ → winHd Wt c lo hi u l) (hQ0 : Q 0 = 1)
    (hcons : ∀ (x : α) (i j : ℤ), (x, i) ∈ Work.OROneRel.winE c lo hi →
      (x, j) ∈ Work.OROneRel.winE c lo hi →
      (levelEl (A := A) (ψ := ψ) Q i)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, i) *
          levelEl (A := A) (ψ := ψ) Q (i + c x) =
        (levelEl (A := A) (ψ := ψ) Q j)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, j) *
          levelEl (A := A) (ψ := ψ) Q (j + c x)) :
    FreeGroup.lift (genX (A := A) (ψ := ψ) hcov Q) w =
      HNNExtension.of (PresentedGroup.mk
        ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))
        (FreeGroup.mk ((Work.OROneRel.decor c 0 (Work.OROneRel.wordOf w)).filterMap
          (Work.OROneRel.winRootStep Wt c lo hi)))) := by
  classical
  set ψg : FreeGroup (Work.OROneRel.winBeta Wt c lo hi) →* winK A ψ :=
    (HNNExtension.of).comp (PresentedGroup.mk
      ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
        Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))) with hψg
  -- the telescoping along the walk of `w`
  have hstep : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf w),
      levelEl (A := A) (ψ := ψ) Q p.1.2 * genX (A := A) (ψ := ψ) hcov Q p.1.1 =
      winGammaK Wt c lo hi u l A ψ p.1 * levelEl (A := A) (ψ := ψ) Q (p.1.2 + c p.1.1) := by
    intro p hp
    exact levelEl_mul_genX (A := A) (ψ := ψ) hcov Q hcons (hwin p hp)
  have ht := Work.OROneRel.walking_telescope (K := winK A ψ) c
    (fun x => genX (A := A) (ψ := ψ) hcov Q x) (fun i => levelEl (A := A) (ψ := ψ) Q i)
    (fun e => winGammaK Wt c lo hi u l A ψ e) (Work.OROneRel.wordOf w) 0 hstep
  -- the `X`-product is the value of the comparison map on `w`
  have hPXgen : ∀ L : List (α × Bool),
      (L.map (fun p => if p.2 then genX (A := A) (ψ := ψ) hcov Q p.1
        else (genX (A := A) (ψ := ψ) hcov Q p.1)⁻¹)).prod =
      FreeGroup.lift (genX (A := A) (ψ := ψ) hcov Q) (FreeGroup.mk L) := by
    intro L
    rw [FreeGroup.lift_mk]
    congr 1
    refine List.map_congr_left (fun p hp => ?_)
    obtain ⟨a, b⟩ := p
    cases b <;> rfl
  have hPX : ((Work.OROneRel.decor c 0 (Work.OROneRel.wordOf w)).map
      (fun p => if p.2 then genX (A := A) (ψ := ψ) hcov Q p.1.1
        else (genX (A := A) (ψ := ψ) hcov Q p.1.1)⁻¹)).prod =
      FreeGroup.lift (genX (A := A) (ψ := ψ) hcov Q) w :=
    (decor_map_sign (genX (A := A) (ψ := ψ) hcov Q) (Work.OROneRel.wordOf w) 0).trans
      ((hPXgen (Work.OROneRel.wordOf w)).trans
        (congrArg (FreeGroup.lift (genX (A := A) (ψ := ψ) hcov Q))
          (Work.OROneRel.mk_wordOf w)))
  -- the coedge product is the class of the filtered walk word
  have hΓ : ((Work.OROneRel.decor c 0 (Work.OROneRel.wordOf w)).map
      (fun p => if p.2 then winGammaK Wt c lo hi u l A ψ p.1
        else (winGammaK Wt c lo hi u l A ψ p.1)⁻¹)).prod =
      HNNExtension.of (PresentedGroup.mk
        ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))
        (FreeGroup.mk ((Work.OROneRel.decor c 0 (Work.OROneRel.wordOf w)).filterMap
          (Work.OROneRel.winRootStep Wt c lo hi)))) := by
    have h1 : ((Work.OROneRel.decor c 0 (Work.OROneRel.wordOf w)).map
        (fun p => if p.2 then winGammaK Wt c lo hi u l A ψ p.1
          else (winGammaK Wt c lo hi u l A ψ p.1)⁻¹)).prod =
        (((Work.OROneRel.decor c 0 (Work.OROneRel.wordOf w)).map
          (fun p => if p.2 then Work.OROneRel.winGammaWord Wt c lo hi p.1
            else (Work.OROneRel.winGammaWord Wt c lo hi p.1)⁻¹)).map ψg).prod := by
      rw [List.map_map]
      congr 1
      refine List.map_congr_left (fun p hp => ?_)
      obtain ⟨⟨a, i⟩, b⟩ := p
      cases b
      · rfl
      · simp only [Function.comp_apply, Bool.false_eq_true, if_false, map_inv]
        rfl
    have h2 := List.prod_hom ((Work.OROneRel.decor c 0 (Work.OROneRel.wordOf w)).map
      (fun p => if p.2 then Work.OROneRel.winGammaWord Wt c lo hi p.1
        else (Work.OROneRel.winGammaWord Wt c lo hi p.1)⁻¹)) ψg
    have h3 := congrArg ψg (Work.OROneRel.winGammaWord_prod_eq_mk
      (Work.OROneRel.decor c 0 (Work.OROneRel.wordOf w)))
    exact h1.trans (h2.trans (h3.trans rfl))
  rw [hΓ, hPX] at ht
  have hlsig : Work.OROneRel.lsig c (Work.OROneRel.wordOf w) = 0 := by
    rw [lsig_wordOf_eq, hcu]
    rfl
  have hV0 : levelEl (A := A) (ψ := ψ) Q 0 = 1 := by
    rw [levelEl, hQ0, map_one, zpow_zero, mul_one]
  rw [hlsig] at ht
  simp only [hV0, zero_add, one_mul, mul_one] at ht
  exact ht

/-- **The relation condition of the two-maps construction, from the pin**: the generator image `X`
kills the relator `u ^ l`. -/
theorem lift_genX_pow {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {u : FreeGroup α} {l : ℕ}
    {A : Subgroup (winHd Wt c lo hi u l)} {ψ : A ≃* A}
    (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (Q : ℤ → winHd Wt c lo hi u l) (hQ0 : Q 0 = 1)
    (hcons : ∀ (x : α) (i j : ℤ), (x, i) ∈ Work.OROneRel.winE c lo hi →
      (x, j) ∈ Work.OROneRel.winE c lo hi →
      (levelEl (A := A) (ψ := ψ) Q i)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, i) *
          levelEl (A := A) (ψ := ψ) Q (i + c x) =
        (levelEl (A := A) (ψ := ψ) Q j)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, j) *
          levelEl (A := A) (ψ := ψ) Q (j + c x)) :
    FreeGroup.lift (genX (A := A) (ψ := ψ) hcov Q) (u ^ l) = 1 := by
  classical
  let ofk : winHd Wt c lo hi u l →* winK A ψ := HNNExtension.of
  let Mk : FreeGroup (Work.OROneRel.winBeta Wt c lo hi) →* winHd Wt c lo hi u l :=
    PresentedGroup.mk ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
      Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))
  let W : FreeGroup (Work.OROneRel.winBeta Wt c lo hi) := FreeGroup.mk
    ((Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u)).filterMap
      (Work.OROneRel.winRootStep Wt c lo hi))
  have hV : W = Work.OROneRel.winRoot Wt c lo hi u :=
    (Work.OROneRel.winRoot_eq Wt c lo hi u).symm
  have hw := lift_genX_word (A := A) (ψ := ψ) (w := u) hcu hwin hcov Q hQ0 hcons
  have h1 : FreeGroup.lift (genX (A := A) (ψ := ψ) hcov Q) (u ^ l) =
      (ofk (Mk W)) ^ l :=
    (map_pow (FreeGroup.lift (genX (A := A) (ψ := ψ) hcov Q)) u l).trans
      (congrArg (fun z => z ^ l) hw)
  have h2 : (ofk (Mk W)) ^ l = ofk (Mk (W ^ l)) :=
    (map_pow (ofk.comp Mk) W l).symm
  have h3 : ofk (Mk (W ^ l)) = ofk (Mk (Work.OROneRel.winRoot Wt c lo hi u ^ l)) :=
    congrArg (fun z => ofk (Mk z)) (congrArg (fun z => z ^ l) hV)
  have h4 : ofk (Mk (Work.OROneRel.winRoot Wt c lo hi u ^ l)) = 1 := by
    show ofk (PresentedGroup.mk
      ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
        Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))
      (Work.OROneRel.winRoot Wt c lo hi u ^ l)) = 1
    rw [PresentedGroup.one_of_mem (Set.mem_singleton
      (Work.OROneRel.winRoot Wt c lo hi u ^ l)), map_one]
  exact h1.trans (h2.trans (h3.trans h4))

end Work.OROneRel
