import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsDefs
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.fixTheta_cube_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- **`e_tilde_sq_fix`** (`NOTES_LEAD_bs_zs_tits.md` §2; design copy
`Work.ZassenhausSuzuki.TitsDesign.e_tilde_sq_fix`).  On the fixed field of `θ` the coordinates of
`∼z_{μ²}` are `(μ, κ·μ²)` for a *single* `κ` (so `κ` cancels in the endgame): for `μ ≠ 0` with
`θ μ = μ`, `e (∼z_{μ²}) = ⟨μ, (e (∼z_1)).b * μ²⟩`, where `∼` is `szTilde hsplit` and
`z_w = zc e w`.  This is the first conjunct of the already proved `e_tilde_zc_fix` with the
hypothesis `λ ≠ 1` dropped (that hypothesis is used only by its second conjunct); the block uses
`szTilde_zc_b`, `szTilde_coord_sq` and `mul_theta_injective` only. -/
theorem e_tilde_sq_fix_zs {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {μ : GaloisField 2 m} (hfix : θ μ = μ) (h0 : μ ≠ 0) :
    e (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e (μ ^ 2))) =
      (⟨μ, (e (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e 1))).b *
        μ ^ 2⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
  have hμ2 : μ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  -- second coordinate
  have hb : (e (Work.ZassenhausSuzuki.szTilde hsplit
        (Work.ZassenhausSuzuki.zc e (μ ^ 2)))).b
      = (e (Work.ZassenhausSuzuki.szTilde hsplit
          (Work.ZassenhausSuzuki.zc e 1))).b * μ ^ 2 :=
    szTilde_zc_b hsplit hzass hθ1 hθodd htorus hμ2
  -- first coordinate
  have hcoord := szTilde_coord_sq hsplit hzass hθ1 hθodd htorus
    (a := Work.ZassenhausSuzuki.zc e (μ ^ 2)) (b := μ ^ 2)
    (by rw [Work.ZassenhausSuzuki.zc_coe]) hμ2
  have ha : (e (Work.ZassenhausSuzuki.szTilde hsplit
      (Work.ZassenhausSuzuki.zc e (μ ^ 2)))).a = μ := by
    refine mul_theta_injective θ hθodd ?_
    have hstep : (e (Work.ZassenhausSuzuki.szTilde hsplit
          (Work.ZassenhausSuzuki.zc e (μ ^ 2)))).a
          * θ ((e (Work.ZassenhausSuzuki.szTilde hsplit
            (Work.ZassenhausSuzuki.zc e (μ ^ 2)))).a) = μ * θ μ :=
      hcoord.trans (by rw [hfix, pow_two])
    simpa only [] using hstep
  exact Work.ZassenhausSuzuki.SzA.ext ha hb

end Work.ZassenhausSuzuki
