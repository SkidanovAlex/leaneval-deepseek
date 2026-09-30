import Mathlib
import Submission.Work.Cohomology.CompatTrans.prodSphereDefs
import Submission.Work.Cohomology.sphereCapContractible

set_option synthInstance.maxHeartbeats 400000

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Topology

namespace Work.Cohomology

noncomputable section

/-!
# `Wset p q = (capA p × capA q) \ {(N_p, N_q)}` is path connected for `p, q ≥ 1`

`Wset p q = Vset p q ∩ Yset p q` is the product of the two caps `capA p ⊆ S^(p+1)`,
`capA q ⊆ S^(q+1)` with the point `(N_p, N_q)` removed.  Both caps are contractible
(`sphereCapContractible`, transported to the subtype-of-the-sphere form by `flatHomeo`), hence
path connected; this file joins any two points of `Wset p q` to the distinguished point
`(u_p, u_q) ∈ Wset p q` (where `u_m ∈ capA m` is the equatorial point `eqPoint m`, which exists
for `m ≥ 1` and is different from the north pole) by moving one coordinate at a time.  The only
care needed is to keep the running point away from the removed base point `(N_p, N_q)`: this is
possible because at least one of the two coordinates is never the corresponding pole during the
two moves.
-/

/-- The cap `capA m ⊆ S^(m+1)` is contractible. -/
lemma contractible_capA (m : ℕ) : ContractibleSpace ↥(capA m) := by
  haveI : ContractibleSpace
      {x : EuclideanSpace ℝ (Fin (m+1)) // x ∈ sphSet (m+1) ∧ x.ofLp (Fin.last m) > -(1/2)} :=
    sphereCapContractible m (1/2) (by norm_num) (by norm_num)
  exact (flatHomeo (q := fun x : EuclideanSpace ℝ (Fin (m+1)) => x ∈ sphSet (m+1))
    (P := fun x => x.ofLp (Fin.last m) > -(1/2))).contractibleSpace

/-- The cap `capA m ⊆ S^(m+1)` is path connected. -/
lemma pathConnectedSpace_capA (m : ℕ) : PathConnectedSpace ↥(capA m) := by
  haveI := contractible_capA m
  infer_instance

/-- The equatorial point `(1, 0, …, 0) ∈ S^(m+1)`; it lies in `capA m` and differs from the north
pole (for `m ≥ 1`). -/
noncomputable def eqPoint (m : ℕ) (hm : 1 ≤ m) : ↥(sphSet (m+1)) :=
  ⟨Work.Morse.snocLp (EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ)) 0, by
    show ‖Work.Morse.snocLp (EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ)) 0‖ = 1
    have hnorm : ‖EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ)‖ = 1 := by
      rw [PiLp.norm_single]; norm_num
    have h2 : ‖Work.Morse.snocLp (EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ)) 0‖ ^ 2 = 1 := by
      rw [Work.Morse.snocLp_norm_sq, hnorm]; norm_num
    rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_one]⟩

lemma eqPoint_last (m : ℕ) (hm : 1 ≤ m) : (eqPoint m hm).1 (Fin.last m) = 0 := by
  show Work.Morse.snocLp (EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ)) 0 (Fin.last m) = 0
  rw [Work.Morse.snocLp_ofLp_last]

lemma eqPoint_mem_capA (m : ℕ) (hm : 1 ≤ m) : eqPoint m hm ∈ capA m := by
  show (eqPoint m hm).1 (Fin.last m) > -(1/2)
  rw [eqPoint_last]; norm_num

lemma eqPoint_ne_sphN (m : ℕ) (hm : 1 ≤ m) : eqPoint m hm ≠ sphN m := by
  intro h
  have h' := congrArg (fun x : ↥(sphSet (m+1)) => x.1 (Fin.last m)) h
  rw [eqPoint_last, sphN_last] at h'
  norm_num at h'

/-- The distinguished point `(u_p, u_q)` of `Wset p q`. -/
noncomputable def hubW (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) : ↥(Wset p q) :=
  ⟨(eqPoint p hp, eqPoint q hq),
    ⟨⟨eqPoint_mem_capA p hp, eqPoint_mem_capA q hq⟩,
      by intro h; exact eqPoint_ne_sphN p hp (congrArg Prod.fst h)⟩⟩

/-- A point of `Wset p q` built from a point of each cap, together with the proof that the pair
is not the base point. -/
def mkW {p q : ℕ} (a₁ : ↥(sphSet (p+1))) (a₂ : ↥(sphSet (q+1)))
    (ha₁ : a₁ ∈ capA p) (ha₂ : a₂ ∈ capA q) (h : (a₁, a₂) ≠ ptP p q) : ↥(Wset p q) :=
  ⟨(a₁, a₂), ⟨⟨ha₁, ha₂⟩, h⟩⟩

/-- For a fixed first coordinate `a₁ ≠ N_p`, moving the second coordinate inside `capA q` stays
in `Wset p q`. -/
def mapFstW {p q : ℕ} (a₁ : ↥(sphSet (p+1))) (ha₁ : a₁ ∈ capA p) (hne₁ : a₁ ≠ sphN p) :
    C(↥(capA q), ↥(Wset p q)) where
  toFun z := mkW a₁ z.1 ha₁ z.2 (by intro h; exact hne₁ (congrArg Prod.fst h))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk continuous_subtype_val

/-- For a fixed second coordinate `a₂ ≠ N_q`, moving the first coordinate inside `capA p` stays
in `Wset p q`. -/
def mapSndW {p q : ℕ} (a₂ : ↥(sphSet (q+1))) (ha₂ : a₂ ∈ capA q) (hne₂ : a₂ ≠ sphN q) :
    C(↥(capA p), ↥(Wset p q)) where
  toFun z := mkW z.1 a₂ z.2 ha₂ (by intro h; exact hne₂ (congrArg Prod.snd h))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.prodMk continuous_const

/-- Any point with first coordinate `≠ N_p` can be joined to the hub `(u_p, u_q)`. -/
lemma joined_hub_of_ne_fst {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (a₁ : ↥(sphSet (p+1))) (ha₁ : a₁ ∈ capA p) (hne₁ : a₁ ≠ sphN p)
    (a₂ : ↥(sphSet (q+1))) (ha₂ : a₂ ∈ capA q) (h : (a₁, a₂) ≠ ptP p q) :
    Joined (mkW a₁ a₂ ha₁ ha₂ h) (hubW p q hp hq) := by
  have hne₂ : eqPoint q hq ≠ sphN q := eqPoint_ne_sphN q hq
  have h1 : Joined (mkW a₁ a₂ ha₁ ha₂ h)
      (mkW a₁ (eqPoint q hq) ha₁ (eqPoint_mem_capA q hq)
        (by intro hh; exact hne₁ (congrArg Prod.fst hh))) :=
    ((pathConnectedSpace_capA q).joined ⟨a₂, ha₂⟩ ⟨eqPoint q hq, eqPoint_mem_capA q hq⟩).map
      (mapFstW (p:=p) (q:=q) a₁ ha₁ hne₁).continuous
  have h2 : Joined (mkW a₁ (eqPoint q hq) ha₁ (eqPoint_mem_capA q hq)
        (by intro hh; exact hne₁ (congrArg Prod.fst hh))) (hubW p q hp hq) := by
    have hh := ((pathConnectedSpace_capA p).joined ⟨a₁, ha₁⟩
      ⟨eqPoint p hp, eqPoint_mem_capA p hp⟩).map
      (mapSndW (p:=p) (q:=q) (eqPoint q hq) (eqPoint_mem_capA q hq) hne₂).continuous
    simpa [mapSndW, mkW, hubW] using hh
  exact h1.trans h2

theorem pathConnected_Wset (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    PathConnectedSpace ↥(Wset p q) := by
  have key : ∀ a : ↥(Wset p q), Joined a (hubW p q hp hq) := by
    intro a
    by_cases hfst : a.1.1 ≠ sphN p
    · exact joined_hub_of_ne_fst hp hq a.1.1 a.2.1.1 hfst a.1.2 a.2.1.2 a.2.2
    · have hN : a.1.1 = sphN p := not_not.mp hfst
      have hsnd : a.1.2 ≠ sphN q := by
        intro h2; exact a.2.2 (Prod.ext hN h2)
      have hneU : eqPoint p hp ≠ sphN p := eqPoint_ne_sphN p hp
      have h1 : Joined a
          (mkW (eqPoint p hp) a.1.2 (eqPoint_mem_capA p hp) a.2.1.2
            (by intro hh; exact hneU (congrArg Prod.fst hh))) := by
        have hh := ((pathConnectedSpace_capA p).joined ⟨a.1.1, a.2.1.1⟩
          ⟨eqPoint p hp, eqPoint_mem_capA p hp⟩).map
          (mapSndW (p:=p) (q:=q) a.1.2 a.2.1.2 hsnd).continuous
        simpa [mapSndW, mkW] using hh
      exact h1.trans (joined_hub_of_ne_fst hp hq (eqPoint p hp) (eqPoint_mem_capA p hp) hneU
        a.1.2 a.2.1.2 (by intro hh; exact hneU (congrArg Prod.fst hh)))
  refine ⟨⟨hubW p q hp hq⟩, fun x y => (key x).trans (key y).symm⟩

end

end Work.Cohomology
