import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.frel_generic_value_eps
import Submission.Work.ZassenhausSuzuki.frel_torus_inv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- A root group `Q` carrying coordinates in Higman's group `A(K,θ)` is non-trivial. -/
private theorem Q_ne_bot_of_szA_equiv {G : Type} [Group G] {Q : Subgroup G}
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m}
    (e : Q ≃* SzA (GaloisField 2 m) θ) : Q ≠ ⊥ := by
  intro hbot
  have h1 : (e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) : Q) = 1 :=
    Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ (e.symm (⟨1, 0⟩ : SzA _ θ)).2))
  have h2 : (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) = 1 := by
    have := congrArg (fun q : Q => e q) h1
    simpa using this
  exact (one_ne_zero : (1 : GaloisField 2 m) ≠ 0) (by simpa using congrArg SzA.a h2)

/-- **HB 11.13 (b), coordinate form of the value of the book's map `f` under the torus
equivariance.**  `frel_generic_value_eps` (HB 11.13 (b)) gives the book's relation `FRel` at
the generic representatives `e.symm (Xrep θ ν)` and `e.symm (Xval θ ν ξ)`; the
anti-equivariance `frel_torus_inv` (`f ∘ h_λ = h_{λ⁻¹} ∘ f`) then transports this relation
along the torus element `h_λ`: if `h_λ (Xrep θ ν) = ⟨a,b⟩`, the point with coordinates
`⟨a,b⟩` stands in the book's relation to `h_{λ⁻¹} (e.symm (Xval θ ν ξ))`. -/
theorem frel_generic_coords {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m}
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {g : Q} (hg : e g = (⟨1, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ))
    (hstruct : t * (((g ^ 2 : Q)) : G) * t = (g : G) * t * (((g⁻¹ : Q)) : G))
    (nu : (GaloisField 2 m)ˣ) (hnu : (nu : GaloisField 2 m) ≠ 1)
    (xi : (GaloisField 2 m)ˣ)
    {a b lam : GaloisField 2 m}
    (hhlam : Work.ZassenhausSuzuki.SzA.hLam θ lam
        (Work.ZassenhausSuzuki.Xrep θ (nu : GaloisField 2 m))
      = (⟨a, b⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ))
    (hlam : lam ≠ 0)
    (hxi : (xi : GaloisField 2 m) * θ (xi : GaloisField 2 m)
      = 1 + ((nu : GaloisField 2 m))⁻¹ * θ (((nu : GaloisField 2 m))⁻¹)) :
    Work.RankOneUniqueness.FRel H t
      (((e.symm (⟨a, b⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)) : Q) : G)
      (((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ lam⁻¹
        (Work.ZassenhausSuzuki.Xval θ (nu : GaloisField 2 m) (xi : GaloisField 2 m))) :
        Q)) : G) := by
  classical
  -- the root group is non-trivial, as it carries coordinates
  have hQ : Q ≠ ⊥ := Q_ne_bot_of_szA_equiv e
  -- HB 11.13 (b) at the generic representatives
  have hbase : Work.RankOneUniqueness.FRel H t
      (((e.symm (Work.ZassenhausSuzuki.Xrep θ (nu : GaloisField 2 m)) : Q)) : G)
      (((e.symm (Work.ZassenhausSuzuki.Xval θ (nu : GaloisField 2 m)
        (xi : GaloisField 2 m)) : Q)) : G) := by
    simpa only [Work.ZassenhausSuzuki.Xrep, Work.ZassenhausSuzuki.Xval] using
      frel_generic_value_eps hsplit hzass h2 htorus hg hstruct nu hnu xi hxi
  -- the torus element `lam` is realised by an element `d ∈ D = twoPoint H t`
  obtain ⟨d, hdD, hdact⟩ := exists_torus_action hsplit hzass htorus (Units.mk0 lam hlam)
  -- anti-equivariance of `f` under the torus action transports the base relation
  have hmain := frel_torus_inv hsplit hzass hQ h2 θ e hdD (Units.mk0 lam hlam) hdact hbase
  -- read off the two coordinates
  have hu : ((Units.mk0 lam hlam : (GaloisField 2 m)ˣ) : GaloisField 2 m) = lam := rfl
  simp only [MulEquiv.apply_symm_apply, Units.val_inv_eq_inv_val, hu] at hmain
  rw [hhlam] at hmain
  exact hmain

end Work.ZassenhausSuzuki
