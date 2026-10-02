import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.excisionDefs
import Submission.Work.RatHurewicz.excisionCompress
import Submission.Work.RatHurewicz.excisionTransfer
import Submission.Work.RatHurewicz.excisionSubtypeBridge
import Submission.Work.RatHurewicz.excisionSubtypeBridgeC
import Submission.Work.RatHurewicz.excisionComponentFact
import Submission.Work.RatHurewicz.excisionRangeBridge
import Submission.Work.RatHurewicz.triadCompression
import Submission.Work.RatHurewicz.subsingleton_relPiVanishing_of_path
import Submission.Work.RatHurewicz.Triad.Translate
import Submission.Work.StemsB.PiMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The assembly of homotopy excision for open triads

This file assembles the proof of `Work.RatHurewicz.excisionRelPiVanishing`:

* the vanishing hypotheses at the single base point `x₀` give, in degree `0`, that points of
  `B ∩ C` reachable inside `B` (resp. `C`) from `x₀` are joined to `x₀` inside `B ∩ C`
  (`hBpc_of_subsingleton`, `hCpc_of_subsingleton`);
* the reduction of tom Dieck's Problem 1
  (`exists_path_in_inter_of_mem_pathComponent`) turns this into the hypotheses `hB0`, `hC0` of
  the triad compression theorem and into the restricted compression properties `hBc`, `hCc`
  (`compressRelBd_of_relPiVanishing`, with the transfer of the vanishing between the two models of
  the pairs `(B, B∩C)` and `(C, B∩C)`, `subsingleton_relPiVanishing_interB/interC`);
* Puppe's theorem `triadCompression` gives the compression of `(F, range ι)` in degrees `≤ p+q+1`;
* `bijective_πmap_setIncl_of_compressRel` converts that into the bijectivity of `πmap` of the
  inclusion of the range, `bijective_πmap_rangeFactorization` gives it for the corestriction, and
  the two are composed.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

open Work.StemsB
open Work.RatHurewicz.Triad

noncomputable section

variable {X : Type} [TopologicalSpace X] {B C : Set X} {x₀ : ↥(B ∩ C)}

/-- The inclusion `B ∩ C → ↥(interB B C)`, as a continuous map. -/
def interBCM (B C : Set X) : C(↥(B ∩ C), ↥(interB B C)) where
  toFun := interBPoint
  continuous_toFun :=
    Continuous.subtype_mk (interInclLeft B C).continuous (fun a => a.2)

/-- The inclusion `B ∩ C → ↥(interC B C)`, as a continuous map. -/
def interCCM (B C : Set X) : C(↥(B ∩ C), ↥(interC B C)) where
  toFun := interCPoint
  continuous_toFun :=
    Continuous.subtype_mk (interInclRight B C).continuous (fun a => a.2)

theorem interBCM_apply (a : ↥(B ∩ C)) : interBCM B C a = interBPoint a := rfl

theorem interCCM_apply (a : ↥(B ∩ C)) : interCCM B C a = interCPoint a := rfl

/-- The two descriptions of the base point of the pair `(B, B ∩ C)` agree. -/
theorem interBPoint_point (a : ↥B) (ha : (a : X) ∈ B ∩ C) :
    (⟨a, ha⟩ : ↥(interB B C)) = interBPoint (B := B) (C := C) ⟨(a : X), ha⟩ := by
  show (⟨a, ha⟩ : ↥(interB B C)) = ⟨⟨(a : X), ha.1⟩, ha⟩
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The two descriptions of the base point of the pair `(C, B ∩ C)` agree. -/
theorem interCPoint_point (a : ↥C) (ha : (a : X) ∈ B ∩ C) :
    (⟨a, ha⟩ : ↥(interC B C)) = interCPoint (B := B) (C := C) ⟨(a : X), ha⟩ := by
  show (⟨a, ha⟩ : ↥(interC B C)) = ⟨⟨(a : X), ha.2⟩, ha⟩
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- **Homotopy excision for open triads** (tom Dieck (6.4.1), Puppe's proof). -/
theorem excisionRelPiVanishing_aux (hB : IsOpen B) (hC : IsOpen C) (hBC : B ∪ C = Set.univ)
    (x₀ : ↥(B ∩ C)) (p q : ℕ)
    (hBvan : ∀ k, k ≤ p → Subsingleton (RelHomotopyGroup (interInclLeft B C) x₀ k))
    (hCvan : ∀ k, k ≤ q → Subsingleton (RelHomotopyGroup (interInclRight B C) x₀ k)) :
    ∀ k, k + 1 ≤ p + q →
      Function.Bijective (πmap (excisionComparison B C x₀) k
        (homotopyFibreBasepoint (interInclLeft B C) x₀)) := by
  classical
  -- the `π₀` content of the vanishing hypotheses
  have hBpc : ∀ a : ↥(B ∩ C), Nonempty (Path (interInclLeft B C x₀) (interInclLeft B C a)) →
      Nonempty (Path x₀ a) :=
    hBpc_of_subsingleton (B := B) (C := C) (x₀ := x₀) (hBvan 0 (Nat.zero_le p))
  have hCpc : ∀ a : ↥(B ∩ C), Nonempty (Path (interInclRight B C x₀) (interInclRight B C a)) →
      Nonempty (Path x₀ a) :=
    hCpc_of_subsingleton (B := B) (C := C) (x₀ := x₀) (hCvan 0 (Nat.zero_le q))
  -- the reduction of Problem 1 after (6.4.1)
  have key : ∀ {y : X}, y ∈ pathComponent (x₀ : X) →
      ((∀ (hyB : y ∈ B), ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ (⟨y, hyB⟩ : ↥B)))
      ∧ (∀ (hyC : y ∈ C), ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ (⟨y, hyC⟩ : ↥C)))
      ∧ (∀ (hyBC : y ∈ B ∩ C), Nonempty (Path x₀ (⟨y, hyBC⟩ : ↥(B ∩ C))))) :=
    fun hy => exists_path_in_inter_of_mem_pathComponent hB hC hBC x₀ hBpc hCpc hy
  -- the `π₀` hypotheses of the triad compression theorem
  have hB0 : ∀ b : ↥B, (b : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ b) := by
    intro b hb
    exact (key hb).1 b.2
  have hC0 : ∀ c : ↥C, (c : X) ∈ pathComponent (x₀ : X) →
      ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ c) := by
    intro c hc
    exact (key hc).2.1 c.2
  -- the restricted compression properties
  have hBc : ∀ d, 1 ≤ d → d ≤ p + 1 → CompressRelBd (interB B C)
      {y : ↥B | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d := by
    refine compressRelBd_of_relPiVanishing (fun x hx => hx.1) p ?_
    intro a k hk
    obtain ⟨η⟩ := (key a.2.2).2.2 a.2.1
    have hpath : Path (interBPoint (B := B) (C := C) x₀)
        (⟨a.1, a.2.1⟩ : ↥(interB B C)) :=
      (η.map (interBCM B C).continuous).cast rfl (interBPoint_point a.1 a.2.1)
    exact subsingleton_relPiVanishing_of_path (A := interB B C) _ _ hpath k
      (subsingleton_relPiVanishing_interB (B := B) (C := C) (a := x₀) (hBvan k hk))
  have hCc : ∀ d, 1 ≤ d → d ≤ q + 1 → CompressRelBd (interC B C)
      {y : ↥C | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d := by
    refine compressRelBd_of_relPiVanishing (fun x hx => hx.1) q ?_
    intro a k hk
    obtain ⟨η⟩ := (key a.2.2).2.2 a.2.1
    have hpath : Path (interCPoint (B := B) (C := C) x₀)
        (⟨a.1, a.2.1⟩ : ↥(interC B C)) :=
      (η.map (interCCM B C).continuous).cast rfl (interCPoint_point a.1 a.2.1)
    exact subsingleton_relPiVanishing_of_path (A := interC B C) _ _ hpath k
      (subsingleton_relPiVanishing_interC (B := B) (C := C) (a := x₀) (hCvan k hk))
  -- Puppe's theorem
  have hT : ∀ n, n ≤ p + q + 1 → CompressRel (Ffibre X C (x₀ : X))
      (Set.range (excisionComparison B C x₀)) n :=
    triadCompression hB hC hBC x₀ p q hBc hCc hB0 hC0
  -- the conclusion
  intro k hk
  have hBbij : Function.Bijective (πmap (setIncl (Set.range (excisionComparison B C x₀))) k
      (rangeFactorization B C x₀ (homotopyFibreBasepoint (interInclLeft B C) x₀))) :=
    bijective_πmap_setIncl_of_compressRel
      (rangeFactorization B C x₀ (homotopyFibreBasepoint (interInclLeft B C) x₀)) (k + 2)
      (fun d hd => hT d (by omega)) k le_rfl
  have hAbij : Function.Bijective (πmap (rangeFactorization B C x₀) k
      (homotopyFibreBasepoint (interInclLeft B C) x₀)) :=
    bijective_πmap_rangeFactorization (B := B) (C := C) (x₀ := x₀) k
  have hfun : ⇑(πmap (excisionComparison B C x₀) k
        (homotopyFibreBasepoint (interInclLeft B C) x₀))
      = fun w => πmap (setIncl (Set.range (excisionComparison B C x₀))) k
            (rangeFactorization B C x₀ (homotopyFibreBasepoint (interInclLeft B C) x₀))
            (πmap (rangeFactorization B C x₀) k
              (homotopyFibreBasepoint (interInclLeft B C) x₀) w) := by
    funext w
    exact πmap_comp_apply (rangeFactorization B C x₀)
      (setIncl (Set.range (excisionComparison B C x₀))) k
      (homotopyFibreBasepoint (interInclLeft B C) x₀) w
  rw [hfun]
  exact hBbij.comp hAbij

end

end Work.RatHurewicz
