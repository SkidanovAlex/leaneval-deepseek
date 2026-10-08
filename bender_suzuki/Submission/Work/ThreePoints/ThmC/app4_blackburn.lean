import Mathlib
import Submission.Work.ThreePoints.ThmC.Baer
import Submission.Work.Coprime.abelian_split
import Submission.Work.Coprime.Internal
import Submission.Work.Coprime.commutator_commutator_eq
import Submission.Work.Coprime.commutator_normal
import Submission.Work.Coprime.fixedPoints_ne_bot_of_isPGroup
import Submission.Work.Coprime.Basic
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.frattini_quotient_elementary
import Submission.Work.PGroup.commutator_le_frattiniIn
import Submission.Work.PGroup.center_eq_centralizer_of_isCriticalSubgroup
import Submission.Work.ThreePoints.ThmC.app4_blackburn_step
import Submission.Work.ThreePoints.ThmC.app4_coprime_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement Pointwise
open Subgroup

namespace Work.ThreePoints.ThmC

/-! ## Helper lemmas for the Blackburn/Thompson-Bender argument (Peterfalvi I App. IV item 4) -/

/-- If `A` normalises both `Q` and `X`, then it normalises their commutator `⁅Q, X⁆`. -/
theorem app4_normalizer_commutator {Γ : Type} [Group Γ] {A Q X : Subgroup Γ}
    (hAQ : A ≤ Subgroup.normalizer (Q : Set Γ)) (hAX : A ≤ Subgroup.normalizer (X : Set Γ)) :
    A ≤ Subgroup.normalizer ((⁅Q, X⁆ : Subgroup Γ) : Set Γ) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAQ ha),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAX ha)]

/-- `N_Γ(H) ≤ N_Γ(Φ(H))`: the Frattini subgroup of `H` is characteristic in `H`, hence is
normalised by everything that normalises `H`. -/
theorem app4_normalizer_le_normalizer_frattiniIn {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Subgroup.normalizer (H : Set Γ) ≤
      Subgroup.normalizer ((Work.PGroup.frattiniIn H : Subgroup Γ) : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  -- conjugation by `g` restricts to an automorphism of `↥H`
  let ψ : ↥H ≃* ↥H :=
    { toFun := fun y => ⟨g * (y : Γ) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (y : Γ)).mp y.2⟩
      invFun := fun y => ⟨g⁻¹ * (y : Γ) * g,
        (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * (y : Γ) * g)).mpr (by
          rw [show g * (g⁻¹ * (y : Γ) * g) * g⁻¹ = (y : Γ) from by group]; exact y.2)⟩
      left_inv := fun y => Subtype.ext (by group)
      right_inv := fun y => Subtype.ext (by group)
      map_mul' := fun x y => Subtype.ext (by
        show g * (↑x * ↑y) * g⁻¹ = (g * ↑x * g⁻¹) * (g * ↑y * g⁻¹)
        group) }
  have hcomp : H.subtype.comp ψ.toMonoidHom = (MulAut.conj g).toMonoidHom.comp H.subtype := by
    ext y
    rfl
  have hpsi : (frattini ↥H).map ψ.toMonoidHom = frattini ↥H :=
    (Subgroup.characteristic_iff_map_eq.mp frattini_characteristic) ψ
  unfold Work.PGroup.frattiniIn
  change Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.map H.subtype (frattini ↥H))
      = Subgroup.map H.subtype (frattini ↥H)
  rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map, hpsi]

/-- `⁅Q, X⁆ ≤ Q` whenever `X` normalises `Q`. -/
theorem app4_commutator_le_of_le_normalizer {Γ : Type} [Group Γ] {Q X : Subgroup Γ}
    (hXQ : X ≤ Subgroup.normalizer (Q : Set Γ)) : ⁅Q, X⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro q hq x hx
  have h1 : ⁅q, x⁆ = q * (x * q⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
  rw [h1]
  exact Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp (hXQ hx) q⁻¹).mp (Q.inv_mem hq))

/-- **(App. IV, Lemma 2.)**  If `⁅Q, X⁆ = Q` and `X` centralises `Φ(Q)`, then `Φ(Q) ≤ Z(Q)`
(the Three Subgroups Lemma / Hall–Witt). -/
theorem app4_frattiniIn_le_centerIn_of_commutator {Γ : Type} [Group Γ] {Q X : Subgroup Γ}
    (hK : ⁅Q, X⁆ = Q) (hXPhi : ⁅X, Work.PGroup.frattiniIn Q⁆ = ⊥) :
    Work.PGroup.frattiniIn Q ≤ Work.PGroup.centerIn Q := by
  -- `Φ(Q)` is normalised by `Q`, hence `⁅Φ(Q), Q⁆ ≤ Φ(Q)`
  have hPhiQ : ⁅Q, Work.PGroup.frattiniIn Q⁆ ≤ Work.PGroup.frattiniIn Q := by
    have htop : (⊤ : Subgroup ↥Q).map Q.subtype = Q := by
      refine le_antisymm (Subgroup.map_subtype_le _) ?_
      intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    have h1 : ⁅(⊤ : Subgroup ↥Q), frattini ↥Q⁆ ≤ frattini ↥Q :=
      Subgroup.commutator_le_right _ _
    have h2 := Subgroup.map_mono (f := Q.subtype) h1
    rw [Subgroup.map_commutator, htop] at h2
    exact h2
  have h1 : ⁅⁅X, Work.PGroup.frattiniIn Q⁆, Q⁆ = ⊥ := by
    rw [hXPhi, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅Work.PGroup.frattiniIn Q, Q⁆, X⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅Work.PGroup.frattiniIn Q, Q⁆, X⁆
        ≤ ⁅Work.PGroup.frattiniIn Q, X⁆ :=
          Subgroup.commutator_mono_left (by rw [Subgroup.commutator_comm]; exact hPhiQ)
      _ = ⁅X, Work.PGroup.frattiniIn Q⁆ := Subgroup.commutator_comm _ _
      _ = ⊥ := hXPhi
  have h3 : ⁅⁅Q, X⁆, Work.PGroup.frattiniIn Q⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hK] at h3
  rw [Work.PGroup.centerIn_eq_inf_centralizer]
  refine le_inf (Work.PGroup.frattiniIn_le Q) ?_
  exact (Subgroup.le_centralizer_iff (H := Q) (K := Work.PGroup.frattiniIn Q)).mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)

/-- A finite `p`-group with `Φ(Q) ≤ Z(Q)` has nilpotency class at most two. -/
theorem app4_class_two_of_frattiniIn_le_centerIn {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ}
    (hp : p.Prime) {Q : Subgroup Γ} (hQp : IsPGroup p Q)
    (h : Work.PGroup.frattiniIn Q ≤ Work.PGroup.centerIn Q) :
    ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q := by
  haveI hfin : Finite ↥Q := Subtype.finite
  refine le_trans (Work.PGroup.commutator_le_frattini hp hQp) ?_
  intro x hx
  have hmem : (x : Γ) ∈ Work.PGroup.centerIn Q := h (Subgroup.mem_map_of_mem Q.subtype hx)
  have hcent : (x : Γ) ∈ Subgroup.centralizer (Q : Set Γ) := by
    rw [Work.PGroup.centerIn_eq_inf_centralizer] at hmem
    exact (Subgroup.mem_inf.mp hmem).2
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact Subgroup.mem_centralizer_iff.mp hcent (y : Γ) y.2

/-- For a nontrivial finite subgroup `Q`, the Frattini subgroup is strictly smaller. -/
theorem app4_card_frattiniIn_lt {Γ : Type} [Group Γ] [Finite Γ] {Q : Subgroup Γ}
    (hQ : Q ≠ ⊥) : Nat.card ↥(Work.PGroup.frattiniIn Q) < Nat.card ↥Q := by
  haveI hfin : Finite ↥Q := Subtype.finite
  haveI hnt : Nontrivial ↥Q := (nontrivial_iff_ne_bot Q).mpr hQ
  obtain ⟨M, hM⟩ := IsCoatomic.exists_coatom (Subgroup ↥Q)
  have hlt : frattini ↥Q < ⊤ := lt_of_le_of_lt (frattini_le_coatom hM) (lt_of_le_of_ne le_top hM.1)
  have h := Subgroup.card_lt_of_lt hlt
  rw [Subgroup.card_top] at h
  unfold Work.PGroup.frattiniIn
  rwa [Subgroup.card_map_of_injective Q.subtype_injective]

/-- Peterfalvi I App. IV, item 4 (Thompson-Bender / Blackburn, p. 210).  Let `p` be an odd prime,
`Q` a `p`-subgroup of a finite group `Γ`, `X` a `p'`-subgroup of `Γ` and `P ≤ Γ` a `p`-subgroup
normalising `X`, with `X` and `P` normalising `Q`.  If `X` centralises the subgroup generated by
the elements of order `p` of `C_Q(P) = Q ⊓ C_Γ(P)`, then `X` centralises `Q`.

Route (source pp. 209-210, internal form so that the subgroup commutator machinery applies):
strong induction on `Nat.card ↥Q` with all data universally quantified.  In a minimal
counterexample every proper subgroup `R ≤ Q` normalised by both `X` and `P` is centralised by `X`
(induction hypothesis, since `Ω₁C_R(P) ≤ Ω₁C_Q(P)` via `Work.PGroup.omega1_mono`), and
`K := ⁅Q,X⁆ = Q`: otherwise `K` is proper and normalised by `X` and `P`, so `⁅X,K⁆ = ⊥`, and the
coprime identity `Work.Coprime.commutator_commutator_eq` (bridged to subgroup commutators by
`FT.commutator_conjAction`) gives `K = ⁅K,X⁆ = ⊥`, so `X` centralises `Q`.
Then `Q/Z(Q)` is elementary abelian by App. IV item 2: `Φ(Q) < Q` is characteristic, so
`⁅X,Φ(Q)⁆ = ⊥`, and Hall-Witt (`Subgroup.commutator_commutator_eq_bot_of_rotate`) with
`⁅⁅Φ(Q),Q⁆,X⁆ ≤ ⁅Φ(Q),X⁆ = ⊥` gives `⁅⁅Q,X⁆,Φ(Q)⁆ = ⊥`, i.e. `Φ(Q) ≤ Z(Q)`; then `Q/Z(Q)` is a
quotient of the elementary abelian `Q/Φ(Q)`.
Finally apply Baer's construction (`baer_group_exists`, App. IV item 3) to the class-`2` odd-order
group `↥Q` with the conjugation action of `U := X ⊔ P`; by item 1(b) (`Work.Coprime.abelian_split`)
the resulting abelian group `G` splits as `G = G⁺ ⊕ C_G(X)` and `[G,X] ≠ 0` because `X` does not
centralise `Q`; `[G,X]` is normalised by `P`, so the `p`-group `[G,X]` has a `P`-fixed element `g`
of order `p` (`Work.Coprime.fixedPoints_ne_bot_of_isPGroup`), which lies outside `C_G(X)`; the
corresponding element of `Q` has order `p`, is fixed by `P`, and is not fixed by `X`, contradicting
the hypothesis. -/
theorem app4_blackburn {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    {Q X P : Subgroup Γ} (hQp : IsPGroup p Q) (hXp : Nat.Coprime (Nat.card X) p)
    (hPp : IsPGroup p P) (hXQ : X ≤ Subgroup.normalizer (Q : Set Γ))
    (hPQ : P ≤ Subgroup.normalizer (Q : Set Γ))
    (hPX : P ≤ Subgroup.normalizer (X : Set Γ))
    (hcent : ⁅X, Work.PGroup.omega1 Γ p (Q ⊓ Subgroup.centralizer (P : Set Γ))⁆ = ⊥) :
    ⁅X, Q⁆ = ⊥ := by
  -- strong induction on `Nat.card ↥Q`, with all data universally quantified
  suffices key : ∀ n : ℕ, ∀ (Q X P : Subgroup Γ),
      Nat.card Q = n → IsPGroup p Q → Nat.Coprime (Nat.card X) p → IsPGroup p P →
      X ≤ Subgroup.normalizer (Q : Set Γ) → P ≤ Subgroup.normalizer (Q : Set Γ) →
      P ≤ Subgroup.normalizer (X : Set Γ) →
      ⁅X, Work.PGroup.omega1 Γ p (Q ⊓ Subgroup.centralizer (P : Set Γ))⁆ = ⊥ →
      ⁅X, Q⁆ = ⊥ from
    key (Nat.card Q) Q X P rfl hQp hXp hPp hXQ hPQ hPX hcent
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q X P hcard hQp hXp hPp hXQ hPQ hPX hcent
    haveI hfinQ : Finite ↥Q := Subtype.finite
    -- (∗) every proper subgroup normalised by both `X` and `P` is centralised by `X`
    have hstar : ∀ R : Subgroup Γ, R ≤ Q → R ≠ Q →
        X ≤ Subgroup.normalizer (R : Set Γ) → P ≤ Subgroup.normalizer (R : Set Γ) →
        ⁅X, R⁆ = ⊥ := by
      intro R hRQ hRne hXR hPR
      have hcardR : Nat.card R < n := by
        rw [← hcard]
        exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hRQ hRne)
      have hcentR : ⁅X, Work.PGroup.omega1 Γ p (R ⊓ Subgroup.centralizer (P : Set Γ))⁆ = ⊥ := by
        refine le_bot_iff.mp (le_trans (Subgroup.commutator_mono_right ?_) (le_of_eq hcent))
        exact Work.PGroup.omega1_mono (inf_le_inf_right _ hRQ)
      exact ih (Nat.card R) hcardR R X P rfl (hQp.to_le hRQ) hXp hPp hXR hPR hPX hcentR
    by_contra hne
    have hKne : ⁅Q, X⁆ ≠ ⊥ := fun h =>
      hne (by rw [Subgroup.commutator_comm X Q]; exact h)
    have hKle : ⁅Q, X⁆ ≤ Q := app4_commutator_le_of_le_normalizer hXQ
    -- Step 1: `⁅Q, X⁆ = Q`
    have hKQ : ⁅Q, X⁆ = Q := by
      by_contra hKQ
      have hXK : X ≤ Subgroup.normalizer ((⁅Q, X⁆ : Subgroup Γ) : Set Γ) :=
        Subgroup.normalizer_commutator_ge_right Q X
      have hPK : P ≤ Subgroup.normalizer ((⁅Q, X⁆ : Subgroup Γ) : Set Γ) :=
        app4_normalizer_commutator hPQ hPX
      have hbot : ⁅X, ⁅Q, X⁆⁆ = ⊥ := hstar ⁅Q, X⁆ hKle hKQ hXK hPK
      rw [Subgroup.commutator_comm X ⁅Q, X⁆] at hbot
      rw [app4_coprime_commutator hp hQp hXp hXQ] at hbot
      exact hKne hbot
    -- Step 2: `Φ(Q) ≤ Z(Q)`
    have hQne : Q ≠ ⊥ := fun h0 => hKne (by rw [hKQ, h0])
    have hPhiZ : Work.PGroup.frattiniIn Q ≤ Work.PGroup.centerIn Q := by
      have hPhiLt := app4_card_frattiniIn_lt (Γ := Γ) hQne
      have hPhiNe : Work.PGroup.frattiniIn Q ≠ Q := by
        intro heq
        rw [heq] at hPhiLt
        exact absurd hPhiLt (lt_irrefl _)
      have hXPhi : X ≤ Subgroup.normalizer ((Work.PGroup.frattiniIn Q : Subgroup Γ) : Set Γ) :=
        le_trans hXQ (app4_normalizer_le_normalizer_frattiniIn Q)
      have hPPhi : P ≤ Subgroup.normalizer ((Work.PGroup.frattiniIn Q : Subgroup Γ) : Set Γ) :=
        le_trans hPQ (app4_normalizer_le_normalizer_frattiniIn Q)
      exact app4_frattiniIn_le_centerIn_of_commutator hKQ
        (hstar (Work.PGroup.frattiniIn Q) (Work.PGroup.frattiniIn_le Q) hPhiNe hXPhi hPPhi)
    -- Step 3: `↥Q` has class at most two; Baer's argument finishes
    have hclass : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q :=
      app4_class_two_of_frattiniIn_le_centerIn hp hQp hPhiZ
    exact (app4_blackburn_step hp hpodd hQp hXp hPp hXQ hPQ hPX hclass hne) hcent

end Work.ThreePoints.ThmC
