import Mathlib
import Submission.Work.DSEQP.Perfection

namespace Work.DSEQP

namespace pPerfection

variable {A : Type*} [CommRing A] {p : ℕ} [Fact p.Prime] [CharP A p]

/-- The "shift" map `A^{1/p^∞} → A^{1/p^∞}`, `of e a ↦ of (e+1) a`.  It is a candidate
inverse to the Frobenius endomorphism. -/
noncomputable def shift : pPerfection A p →+* pPerfection A p :=
  Ring.DirectLimit.lift (fun _ : ℕ => A) (fun i j _ => ⇑(frobPowHom A p (j - i)))
    (pPerfection A p) (fun i => of (A := A) (p := p) (i + 1))
    (by
      intro i j hij x
      have h : of (A := A) (p := p) (j + 1) (frobPowHom A p (j + 1 - (i + 1)) x)
          = of (A := A) (p := p) (i + 1) x :=
        of_f (A := A) (p := p) (i := i + 1) (j := j + 1) (Nat.succ_le_succ hij) x
      rw [show j + 1 - (i + 1) = j - i from by omega] at h
      exact h)

/-- The Frobenius endomorphism of the perfection, `of e a ↦ of e (a ^ p)`. -/
noncomputable def frobHom : pPerfection A p →+* pPerfection A p :=
  Ring.DirectLimit.lift (fun _ : ℕ => A) (fun i j _ => ⇑(frobPowHom A p (j - i)))
    (pPerfection A p) (fun i => (of (A := A) (p := p) i).comp (frobenius A p))
    (by
      intro i j hij x
      simp only [RingHom.comp_apply, frobenius_def]
      rw [← map_pow (frobPowHom A p (j - i)) x p]
      exact of_f (A := A) (p := p) hij (x ^ p))

theorem shift_of (i : ℕ) (x : A) :
    shift (A := A) (p := p) (of (A := A) (p := p) i x)
      = of (A := A) (p := p) (i + 1) x := by
  simp only [shift, of]
  rw [Ring.DirectLimit.lift_of]

theorem frobHom_of (i : ℕ) (x : A) :
    frobHom (A := A) (p := p) (of (A := A) (p := p) i x)
      = of (A := A) (p := p) i (x ^ p) := by
  simp only [frobHom, of]
  rw [Ring.DirectLimit.lift_of]
  simp [RingHom.comp_apply, frobenius_def]

theorem frobHom_comp_shift :
    (frobHom (A := A) (p := p)).comp (shift (A := A) (p := p))
      = RingHom.id (pPerfection A p) := by
  apply Ring.DirectLimit.hom_ext
  intro i
  ext x
  simp only [RingHom.comp_apply, RingHom.id_apply]
  change frobHom (A := A) (p := p) (shift (A := A) (p := p) (of (A := A) (p := p) i x))
      = of (A := A) (p := p) i x
  rw [shift_of, frobHom_of, map_pow (of (A := A) (p := p) (i + 1)) x p, of_succ_pow]

theorem shift_comp_frobHom :
    (shift (A := A) (p := p)).comp (frobHom (A := A) (p := p))
      = RingHom.id (pPerfection A p) := by
  apply Ring.DirectLimit.hom_ext
  intro i
  ext x
  simp only [RingHom.comp_apply, RingHom.id_apply]
  change shift (A := A) (p := p) (frobHom (A := A) (p := p) (of (A := A) (p := p) i x))
      = of (A := A) (p := p) i x
  rw [frobHom_of, shift_of, map_pow (of (A := A) (p := p) (i + 1)) x p, of_succ_pow]

theorem frobHom_apply (z : pPerfection A p) :
    frobHom (A := A) (p := p) z = z ^ p := by
  refine Ring.DirectLimit.induction_on z (fun i x => ?_)
  change frobHom (A := A) (p := p) (of (A := A) (p := p) i x)
      = (of (A := A) (p := p) i x) ^ p
  rw [frobHom_of, map_pow]

theorem bijective_pow :
    Function.Bijective (fun x : pPerfection A p => x ^ p) := by
  have hSF : ∀ z : pPerfection A p,
      shift (A := A) (p := p) (frobHom (A := A) (p := p) z) = z :=
    fun z => congrArg (fun f : pPerfection A p →+* pPerfection A p => f z)
      (shift_comp_frobHom (A := A) (p := p))
  have hFS : ∀ z : pPerfection A p,
      frobHom (A := A) (p := p) (shift (A := A) (p := p) z) = z :=
    fun z => congrArg (fun f : pPerfection A p →+* pPerfection A p => f z)
      (frobHom_comp_shift (A := A) (p := p))
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h2 : frobHom (A := A) (p := p) x = frobHom (A := A) (p := p) y := by
      rw [frobHom_apply, frobHom_apply]
      simpa using hxy
    calc x = shift (A := A) (p := p) (frobHom (A := A) (p := p) x) := (hSF x).symm
      _ = shift (A := A) (p := p) (frobHom (A := A) (p := p) y) := by rw [h2]
      _ = y := hSF y
  · intro y
    refine ⟨shift (A := A) (p := p) y, ?_⟩
    show (shift (A := A) (p := p) y) ^ p = y
    rw [← frobHom_apply]
    exact hFS y

end pPerfection

theorem perfectRing_pPerfection (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p] :
    PerfectRing (pPerfection A p) p :=
  PerfectRing.mk (pPerfection.bijective_pow (A := A) (p := p))

end Work.DSEQP
