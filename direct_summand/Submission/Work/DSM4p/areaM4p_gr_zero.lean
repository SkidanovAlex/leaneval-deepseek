import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSM2p.isReduced

universe a

namespace Work.DSM4p

open DSMap DSMap.Mix DSMap.Mix2

/-!
# `Work.DSM4p.areaM4p_gr_zero`

The degenerate case `gr 0 = 0` of the Riemann extension tower `area_M4p`: if the chosen system
of `p`-power roots of `g = gr 0` starts at `0`, then the whole system vanishes
(`gr k ^ (p ^ k) = gr 0 = 0` and a perfectoid ring is reduced, `Work.DSM2p.isReduced Q`),
and the tower can be taken to be the constant tower of the zero ring `B ⧸ ⊤`, in which every
`PerfectoidData` field, the divisibility `g ∣ p ^ n`, the `ϖ`-compatibility and both clauses of
`IsQRETp` are trivial.
-/

/-- The `PerfectoidData` structure on a subsingleton commutative ring.  All the fields are
equations (or existentials of equations) in a subsingleton ring, and `IsAdicComplete` has the
`Subsingleton` instance, so this is `Subsingleton.elim` throughout. -/
private def subsingletonPerfectoidData (p : ℕ) (A : Type a) [CommRing A] [Subsingleton A] :
    DSMap.PerfectoidData p A where
  ϖ := fun _ => 0
  root := fun _ => Subsingleton.elim _ _
  unit := ⟨1, Subsingleton.elim _ _⟩
  torsionFree := fun x y _ => Subsingleton.elim x y
  complete := inferInstance
  frobSurj := fun x => ⟨x, by
    rw [show x - x ^ p = 0 from Subsingleton.elim _ _]
    exact Ideal.zero_mem _⟩
  frobInj := fun y _ => by
    rw [show y = 0 from Subsingleton.elim _ _]
    exact Ideal.zero_mem _

/-- In a subsingleton ring every element lies in every ideal. -/
private lemma subsingleton_mem_ideal {A : Type a} [Ring A] [Subsingleton A] (I : Ideal A)
    (x : A) : x ∈ I := by
  rw [show x = 0 from Subsingleton.elim _ _]
  exact Ideal.zero_mem I

theorem areaM4p_gr_zero {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (Q : DSMap.PerfectoidData p B) (gr : ℕ → B) (hgr : Work.DSM4p.IsRootSystem p gr)
    (hgr0 : gr 0 = 0) : Work.DSM4p.AreaM4p p B Q gr := by
  -- `B` is reduced, so the vanishing of `gr 0` propagates to the whole root system:
  -- `gr k ^ (p ^ k) = gr 0 = 0`.
  have hred : IsReduced B := Work.DSM2p.isReduced Q
  have hgrk : ∀ k, gr k = 0 := fun k =>
    hred.eq_zero (gr k) ⟨p ^ k, by rw [hgr.pow_pow_zero k, hgr0]⟩
  -- The tower: the constant tower of the zero ring `B ⧸ ⊤`.
  refine (areaM4p_iff p B Q gr).mpr ⟨{
    D := fun _ => B ⧸ (⊤ : Ideal B)
    QD := fun n => subsingletonPerfectoidData p (B ⧸ (⊤ : Ideal B))
    tr := fun n => AlgHom.id B (B ⧸ (⊤ : Ideal B))
    varpi_eq := fun n k => Subsingleton.elim _ _
    dvd := fun n => ⟨0, Subsingleton.elim _ _⟩
    qret := ?_ }⟩
  -- Both clauses of `IsQRETp` are trivial: the kernel clause because `gr k = 0`, the cokernel
  -- clause because every level `D n` is a subsingleton.
  intro m k
  refine ⟨0, ?_, ?_⟩
  · intro n x _
    have h : Q.ϖ k * gr k * x = 0 := by simp [hgrk k]
    rw [h]
    exact Ideal.zero_mem _
  · intro n y
    refine ⟨0, ?_⟩
    exact subsingleton_mem_ideal _ _

end Work.DSM4p
