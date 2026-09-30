import Mathlib
import Submission.Work.Pi6.MSS.e1CohDualDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The differential of a section lift lands in the next filtration step

If `y` is a cochain of the singular complex of `E` which, on the chains of the `(s+1)`-st Serre
subcomplex `C(A_{s+1})`, agrees with a linear functional `ψ` on the `s`-th graded piece
`C(A_{s+1})/C(A_s)` (`hyπ`), and if `ψ` kills the boundaries of that graded piece (`hbdry`), then
the transposed differential `dPrev y = δy` lies one step deeper in the Serre filtration, i.e. in
`F^{s+1}`.

Indeed, for `w` a chain of `C(A_{s+1})` in degree `n+1`,
`δy(w) = y(∂w) = ψ(π ∂w) = ψ(d π w) = 0`, using that `π` is a chain map and `hbdry`.
-/

namespace Work.Pi6.MSS.e1CohDual

theorem secLiftDMem (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s n : ℕ) (ψ : (Work.Pi6.MSS.e1cKg 𝕜 p s).X n →ₗ[𝕜] 𝕜)
    (y : (Work.Pi6.MSS.serreCF 𝕜 E B p).C.X n)
    (hyπ : ∀ v : (Work.Pi6.MSS.e1cCc 𝕜 p (s+1)).X n,
      (Work.Pi6.MSS.e1cCochFun 𝕜 p n y)
        (((Work.Pi6.MSS.e1cIncl 𝕜 p (s+1)).f n).hom v)
      = ψ (((Work.Pi6.MSS.e1cKgπ 𝕜 p s).f n).hom v))
    (hbdry : ∀ v : (Work.Pi6.MSS.e1cKg 𝕜 p s).X (n+1),
      ψ (((Work.Pi6.MSS.e1cKg 𝕜 p s).d (n+1) n).hom v) = 0) :
    (Work.Pi6.MSS.serreCF 𝕜 E B p).dPrev (n+1) y ∈
      (Work.Pi6.MSS.serreCF 𝕜 E B p).F (s+1) (n+1) := by
  -- It suffices that `dPrev y` kills the chains of `C(A_{s+1})` in degree `n+1`.
  apply Work.Pi6.MSS.e1cF_of_kill 𝕜 p (s+1) (n+1)
  intro w
  -- `(dPrev y)(incl w) = y (∂ (incl w)) = y (incl (∂ w))`
  rw [Work.Pi6.MSS.e1cW_dPrev_apply 𝕜 p n y
    (((Work.Pi6.MSS.e1cIncl 𝕜 p (s+1)).f (n+1)).hom w)]
  rw [Work.Pi6.MSS.e1cIncl_d_apply 𝕜 p (s+1) n w]
  -- ... and `y` agrees with `ψ ∘ π` on `C(A_{s+1})`
  have hyπ' := hyπ (((Work.Pi6.MSS.e1cCc 𝕜 p (s+1)).d (n+1) n).hom w)
  simp only [Work.Pi6.MSS.e1cCochFun] at hyπ' ⊢
  rw [hyπ']
  -- `π` is a chain map, so `π (∂ w) = d (π w)`, and `ψ` kills the boundary `d (π w)`.
  have hcomm : ((Work.Pi6.MSS.e1cKgπ 𝕜 p s).f n).hom
      (((Work.Pi6.MSS.e1cCc 𝕜 p (s+1)).d (n+1) n).hom w)
      = ((Work.Pi6.MSS.e1cKg 𝕜 p s).d (n+1) n).hom
        (((Work.Pi6.MSS.e1cKgπ 𝕜 p s).f (n+1)).hom w) := by
    have h := congrArg
      (fun (g : (Work.Pi6.MSS.e1cCc 𝕜 p (s+1)).X (n+1) ⟶
          (Work.Pi6.MSS.e1cKg 𝕜 p s).X n) => g.hom w)
      (Work.Pi6.MSS.e1cKgπ_comm 𝕜 p s n)
    exact h.symm
  rw [hcomm]
  exact hbdry (((Work.Pi6.MSS.e1cKgπ 𝕜 p s).f (n+1)).hom w)

end Work.Pi6.MSS.e1CohDual
