import Mathlib
import Submission.Work.SSGRoute.gradedStep_diagonal
import Submission.Work.SSGRoute.two_torsion_assembly
import Submission.Work.SSGRoute.zz3.Defs
import Submission.Work.SSGRoute.zz3.LamTProps
import Submission.Work.SSGRoute.zz3.ThetaProps
import Submission.Work.SSGRoute.zz3.ThetaSurj
import Submission.Work.SSGRoute.zz3.ThetaKer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `(3,3)` diagonal graded step at `G = ℤ/2`

The graded piece `E(3,3)` of the refined `2`-central filtration of `F(n)` (for
`G = Multiplicative (ZMod 2)`) is a free module over `𝔽₂[C₂]`, hence `ker (1+δ) = im (1+δ)`
there; every anti-fixed element of the graded piece is therefore a `δ`-difference.

Route.  `TT n` (the degree-`3` part of the free associative algebra mod `2`) is a free
`𝔽₂[C₂]`-module (`dTT_decomp`), `Λ = LamT n` is an equivariant idempotent retraction onto the
degree-`3` Lie part (`LamTProps`), and `θ = thetaFun n` ("product of the classes of the
left-nested brackets `[[x,y],z]`") restricts to an isomorphism `im Λ ≅ E(3,3)`
(`ThetaSurj`, `ThetaKer`).  A `δ`-fixed `c ∈ E(3,3)` has a `Λ`-fixed preimage `g`, which is
`δ`-fixed, hence `g = u + δu`, and `c = θ u · δ(θ u)` is then a `δ`-difference.
-/

open scoped commutatorElement
open Work.CohomologicalShrinking

namespace Work.SSGRoute

namespace ZZ3

theorem gs3_LamT_add (n : ℕ) (g h : TT n) : LamT n (g + h) = LamT n g + LamT n h := by
  funext w
  simp only [LamT_apply, Pi.add_apply]
  ring

/-- The left-nested commutator of a nonempty list of generators lies in the corresponding term of
the lower central series (Mathlib indexing). -/
theorem gs3_lc_mem {X : Type*} (L : List X) (hL : 1 ≤ L.length) :
    Work.SSGRoute.prop5.lc L ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (L.length - 1) := by
  cases L with
  | nil => simp at hL
  | cons x rest =>
      rw [Work.SSGRoute.prop5.lc_eq_gpFold]
      have h := Work.SSGRoute.prop5.gpFold_mem (X := X) rest 1 le_rfl
        (u := FreeGroup.of x) (Subgroup.mem_top _)
      simpa using h

theorem gs3_lcF_mem (n : ℕ) (w : Idx n) :
    lcF n w ∈ (⊤ : Subgroup (FreeGroup (XX n))).lowerCentralSeries 2 := by
  have h := gs3_lc_mem (X := XX n) (List.ofFn w) (by rw [List.length_ofFn]; norm_num)
  rw [List.length_ofFn] at h
  exact h

theorem gs3_lcF_mem_flowTerm (n : ℕ) (w : Idx n) : lcF n w ∈ flowTerm 2 Gm n 3 3 := by
  show lcF n w ∈ Work.CohomologicalShrinking.refinedTerm 2
    (Work.Shrinking.freeOperatorGroup Gm n) 3 3
  rw [Work.CohomologicalShrinking.refinedTerm]
  exact Subgroup.mem_sup_left
    ⟨Work.SSGRoute.zz3.lcF_mem n w, gs3_lcF_mem n w⟩

theorem gs3_mkQ_mem_ker (n : ℕ) (w : Idx n) :
    mkQ n (lcF n w) ∈ (flowQuotSucc 2 Gm n 3 3).ker :=
  mem_ker_of_mem_flowTerm Gm n 3 (lcF n w) (gs3_lcF_mem_flowTerm n w)

/-- Every element of the kernel is a value of `thetaFun`, hence has order dividing `2`. -/
theorem gs3_sq_eq_one_of_mem_ker (n : ℕ)
    (c : flowQuotient 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2)
    (hc : c ∈ (flowQuotSucc 2 Gm n 3 3).ker) : c * c = 1 := by
  obtain ⟨g, -, hgc⟩ := Work.SSGRoute.zz3.ThetaSurj n c hc
  rw [← hgc, ← (Work.SSGRoute.zz3.ThetaProps n).2.1 g g]
  have hgg : g + g = 0 := by
    funext w
    exact CharTwo.add_self_eq_zero (g w)
  rw [hgg, (Work.SSGRoute.zz3.ThetaProps n).1]

/-- The kernel of the projection `Q_{(4,1)} → Q_{(3,3)}` is abelian. -/
theorem gs3_mul_comm_of_mem_ker (n : ℕ)
    (a c : flowQuotient 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2)
    (h : c ∈ (flowQuotSucc 2 Gm n 3 3).ker) : a * c = c * a := by
  have h1 := flowQuotSucc_ker_central (p := 2) (G := Gm) n 3 3 a c h
  have h2 : a * c = (a * c * a⁻¹) * a := by group
  rw [h2, h1]

theorem gs3_thetaFun_mem_ker (n : ℕ) (g : TT n) :
    thetaFun n g ∈ (flowQuotSucc 2 Gm n 3 3).ker := by
  rw [thetaFun]
  refine (Subgroup.list_prod_mem _) ?_
  intro y hy
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hy
  exact Subgroup.pow_mem _ (gs3_mkQ_mem_ker n w) _

end ZZ3

theorem gradedStep_diagonal_zmodTwo_three (n : ℕ) :
    ∀ c : Work.CohomologicalShrinking.flowQuotient 2 (Multiplicative (ZMod 2)) n
        (Work.CohomologicalShrinking.tauSucc 3 3).1 (Work.CohomologicalShrinking.tauSucc 3 3).2,
      Work.SSGRoute.flowQuotSucc 2 (Multiplicative (ZMod 2)) n 3 3 c = 1 →
      Work.CohomologicalShrinking.flowAction 2 (Multiplicative (ZMod 2)) n
        (Work.CohomologicalShrinking.tauSucc 3 3).1 (Work.CohomologicalShrinking.tauSucc 3 3).2
        (Multiplicative.ofAdd (1 : ZMod 2)) c = c⁻¹ →
      ∃ e : Work.CohomologicalShrinking.flowQuotient 2 (Multiplicative (ZMod 2)) n
            (Work.CohomologicalShrinking.tauSucc 3 3).1
            (Work.CohomologicalShrinking.tauSucc 3 3).2,
        c = (Work.CohomologicalShrinking.flowAction 2 (Multiplicative (ZMod 2)) n
              (Work.CohomologicalShrinking.tauSucc 3 3).1
              (Work.CohomologicalShrinking.tauSucc 3 3).2
              (Multiplicative.ofAdd (1 : ZMod 2)) e)⁻¹ * e := by
  intro c hc hanti
  have hmem : c ∈ (flowQuotSucc 2 ZZ3.Gm n 3 3).ker := MonoidHom.mem_ker.mpr hc
  obtain ⟨g, hgL, hgc⟩ := Work.SSGRoute.zz3.ThetaSurj n c hmem
  have hcsq : c * c = 1 := ZZ3.gs3_sq_eq_one_of_mem_ker n c hmem
  have hfixc : flowAction 2 ZZ3.Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 ZZ3.dm c = c := by
    rw [hanti, inv_eq_of_mul_eq_one_right hcsq]
  have hgd : ZZ3.dTT n g = g := by
    have h1 : ZZ3.thetaFun n (g + ZZ3.dTT n g) = 1 := by
      rw [(Work.SSGRoute.zz3.ThetaProps n).2.1 g (ZZ3.dTT n g),
        (Work.SSGRoute.zz3.ThetaProps n).2.2 g, hgc, hfixc, hcsq]
    have h2 : ZZ3.LamT n (g + ZZ3.dTT n g) = g + ZZ3.dTT n g := by
      rw [ZZ3.gs3_LamT_add, hgL, (Work.SSGRoute.zz3.LamTProps n).2 g, hgL]
    have h3 := Work.SSGRoute.zz3.ThetaKer n (g + ZZ3.dTT n g) h2 h1
    have hgg : g + g = 0 := by
      funext w
      exact CharTwo.add_self_eq_zero (g w)
    have h5 : g + ZZ3.dTT n g = g + g := by rw [h3, hgg]
    exact add_left_cancel h5
  obtain ⟨u, hu⟩ := ZZ3.dTT_decomp n g hgd
  refine ⟨ZZ3.thetaFun n u, ?_⟩
  have hkey : (flowAction 2 ZZ3.Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 ZZ3.dm
        (ZZ3.thetaFun n u))⁻¹ * ZZ3.thetaFun n u
      = ZZ3.thetaFun n u * flowAction 2 ZZ3.Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 ZZ3.dm
          (ZZ3.thetaFun n u) := by
    have hdmem : flowAction 2 ZZ3.Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 ZZ3.dm
        (ZZ3.thetaFun n u) ∈ (flowQuotSucc 2 ZZ3.Gm n 3 3).ker := by
      have h1 : ZZ3.thetaFun n (ZZ3.dTT n u) ∈ (flowQuotSucc 2 ZZ3.Gm n 3 3).ker :=
        ZZ3.gs3_thetaFun_mem_ker n (ZZ3.dTT n u)
      rwa [(Work.SSGRoute.zz3.ThetaProps n).2.2 u] at h1
    have hcomm := ZZ3.gs3_mul_comm_of_mem_ker n
      (flowAction 2 ZZ3.Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 ZZ3.dm (ZZ3.thetaFun n u))
      (ZZ3.thetaFun n u) (ZZ3.gs3_thetaFun_mem_ker n u)
    have hsq : (flowAction 2 ZZ3.Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 ZZ3.dm
        (ZZ3.thetaFun n u)) * (flowAction 2 ZZ3.Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 ZZ3.dm
        (ZZ3.thetaFun n u)) = 1 := ZZ3.gs3_sq_eq_one_of_mem_ker n _ hdmem
    rw [inv_eq_of_mul_eq_one_right hsq]
    exact hcomm
  rw [← hgc, hu, (Work.SSGRoute.zz3.ThetaProps n).2.1 u (ZZ3.dTT n u),
    (Work.SSGRoute.zz3.ThetaProps n).2.2 u]
  exact hkey.symm

end Work.SSGRoute
