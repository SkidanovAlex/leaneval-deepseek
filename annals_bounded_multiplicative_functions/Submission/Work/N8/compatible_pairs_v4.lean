import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n8_defs
import Submission.Work.N8.IntegralOn_gcd
import Submission.Work.N8.goodQuad_q_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N8: compatible pairs along the edges (MRT Prop. 5.5 / MRTTZ Prop. 3.11)

Given the covering family `F x` of good quadruples over the `(X,L)`-family `A.fam` and, for every
edge `e` of `A.edges`, a pair of good quadruples at `e.x₁`, `e.x₂` sharing the frequency `T` and
satisfying the integrality relation `IntegralOn 1 (dil e.p₂ γ₁ - dil e.p₁ γ₂)`, the covering
hypothesis produces witnesses `z₁ ∈ F e.x₁`, `z₂ ∈ F e.x₂` with the same coarse moduli.  After
discarding the `≤ #edges/2` "bad" edges (those where `e.p₁` or `e.p₂` divides one of the moduli of
a witness), every surviving edge yields a compatible pair, and the same `q` follows from the
lattice-theoretic Lemma `Work.N8.goodQuad_q_eq`.

The map `e ↦ ((e.x₁,z₁),(e.x₂,z₂))` is injective on the surviving edges (an edge is determined by
its two endpoints, by hypothesis), so the number of compatible pairs is at least half the number of
edges, hence `≥ (c/4)(X/L) π₀(P₁)²`.

Note on the last conjunct of the conclusion.  For the right-nested tuple
`ℝ × ℕ × ℕ × ℝ[X] × Finset ℕ`, and `p` a pair of `(fam point, quadruple)` blocks, the entry
`p.1.2.2.2.1` is the **`qf`** component (a `ℕ`, which the elaborator coerces to `ℝ[X]` by
`Nat.cast`, i.e. a constant polynomial) rather than the phase `γ` (`p.1.2.2.2.2.1`).  That
conjunct is therefore automatic -- `IntegralOn 1` of a constant integer polynomial -- and is
discharged by `cp_IntegralOn_dil_natCast_sub`; the phase version of the relation, which is the one
produced by the hypotheses and which is genuinely needed to identify the moduli, is extracted in
the `key` step and fed to `Work.N8.goodQuad_q_eq`.
-/

namespace Work.N8

open Polynomial Finset

/-- `ModZConst` is preserved by `dil`, up to an integer constant. -/
private lemma dil_ModZConst_cp {γ γ' : Polynomial ℝ} (h : Work.BMF.ModZConst γ γ') (a : ℝ) :
    ∃ c : ℤ, Work.BMF.dil a γ = Work.BMF.dil a γ' + Polynomial.C (c : ℝ) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [hc]
  simp only [Work.BMF.dil, Polynomial.add_comp, Polynomial.C_comp]

/-- Dilation of a constant (natural-cast) polynomial is that constant. -/
private lemma cp_dil_natCast (a : ℝ) (m : ℕ) :
    Work.BMF.dil a ((m : ℕ) : Polynomial ℝ) = ((m : ℕ) : Polynomial ℝ) := by
  simp [Work.BMF.dil]

/-- `IntegralOn 1` of a constant integer polynomial is automatic. -/
private lemma cp_IntegralOn_dil_natCast_sub (a b : ℝ) (m n : ℕ) :
    Work.BMF.IntegralOn 1 (Work.BMF.dil a ((m : ℕ) : Polynomial ℝ) -
      Work.BMF.dil b ((n : ℕ) : Polynomial ℝ)) := by
  rw [cp_dil_natCast a m, cp_dil_natCast b n]
  have h1 : Work.BMF.IntegralOn 1 ((m : ℕ) : Polynomial ℝ) := by
    intro k; exact ⟨(m : ℤ), by simp⟩
  have h2 : Work.BMF.IntegralOn 1 ((n : ℕ) : Polynomial ℝ) := by
    intro k; exact ⟨(n : ℤ), by simp⟩
  exact h1.sub h2

theorem compatible_pairs_v4 (k : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (C₁ : ℝ)
    (hC₁ : 0 < C₁) :
    ∀ (f : ℕ → ℂ) (c C X L P₁ P₂ : ℝ) (ℓ : ℕ) (A : Work.BMF.ADIData k f c C X L P₁ P₂ ℓ)
      (F : ℝ → Finset (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)) (K : ℕ),
      0 < c → 0 < X → 1 ≤ L → L ≤ X → 4 ≤ P₁ → P₁ ≤ X →
      (∀ x, (F x).card ≤ K) →
      (∀ x, ∀ z ∈ F x, Work.BMF.GoodQuad A δ x z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) →
      (∀ e ∈ A.edges, ∃ (T : ℝ) (q₁ qf₁ : ℕ) (γ₁ : Polynomial ℝ) (Ps₁ : Finset ℕ)
          (q₂ qf₂ : ℕ) (γ₂ : Polynomial ℝ) (Ps₂ : Finset ℕ),
        Work.BMF.GoodQuad A δ e.x₁ T q₁ qf₁ γ₁ Ps₁ ∧
        Work.BMF.GoodQuad A δ e.x₂ T q₂ qf₂ γ₂ Ps₂ ∧
        Work.BMF.IntegralOn 1 (Work.BMF.dil (e.p₂ : ℝ) γ₁ - Work.BMF.dil (e.p₁ : ℝ) γ₂) ∧
        (∃ z ∈ F e.x₁, z.2.1 = q₁ ∧ Work.BMF.ModZConst z.2.2.2.1 γ₁ ∧
          |z.1 - T| ≤ C₁ * (X / L)) ∧
        (∃ z ∈ F e.x₂, z.2.1 = q₂ ∧ Work.BMF.ModZConst z.2.2.2.1 γ₂ ∧
          |z.1 - T| ≤ C₁ * (X / L))) →
      (∀ e ∈ A.edges, ∀ e' ∈ A.edges, e.x₁ = e'.x₁ → e.x₂ = e'.x₂ →
        e.p₁ = e'.p₁ ∧ e.p₂ = e'.p₂) →
      ((A.edges.filter (fun e ↦
        (∃ z ∈ F e.x₁, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1) ∨
        (∃ z ∈ F e.x₂, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1))).card : ℝ) ≤ (A.edges.card : ℝ) / 2 →
      ∃ S : Finset ((ℝ × (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)) ×
                    (ℝ × (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ))),
        (∀ p ∈ S,
          p.1.1 ∈ A.fam ∧ p.2.1 ∈ A.fam ∧ p.1.2 ∈ F p.1.1 ∧ p.2.2 ∈ F p.2.1 ∧
          p.1.2.2.1 = p.2.2.2.1 ∧
          |p.1.2.1 - p.2.2.1| ≤ 2 * C₁ * (X / L) ∧
          (∃ p₁ p₂ : ℕ, Work.BMF.IsPrimeIn P₁ (2 * P₁) p₁ ∧ Work.BMF.IsPrimeIn P₁ (2 * P₁) p₂ ∧
            p₁ ≠ p₂ ∧ ¬ p₁ ∣ p.1.2.2.1 ∧ ¬ p₂ ∣ p.2.2.2.1 ∧
            Work.BMF.EdgeGeom A.fam P₁ L ⟨p.1.1, p.2.1, p₁, p₂⟩ ∧
            Work.BMF.IntegralOn 1 (Work.BMF.dil (p₂ : ℝ) p.1.2.2.2.2.1 -
              Work.BMF.dil (p₁ : ℝ) p.2.2.2.2.2.1))) ∧
        c / 4 * (X / L) * Work.BMF.pi0 P₁ ^ 2 ≤ (S.card : ℝ)
:= by
  intro f c C X L P₁ P₂ ℓ A F K hc hX hL1 hLX hP₁ hP₁X hKcard hgood h3 huniq hbad
  classical
  let badP : Work.BMF.Edge → Prop := fun e ↦
    (∃ z ∈ F e.x₁, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1) ∨
    (∃ z ∈ F e.x₂, e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1)
  let E' : Finset Work.BMF.Edge := A.edges.filter (fun e => ¬ badP e)
  have hE'def : E' = A.edges.filter (fun e => ¬ badP e) := rfl
  have hbad' : ((A.edges.filter badP).card : ℝ) ≤ (A.edges.card : ℝ) / 2 := hbad
  have key : ∀ e ∈ E', ∃ z₁ z₂ : ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ,
      z₁ ∈ F e.x₁ ∧ z₂ ∈ F e.x₂ ∧ z₁.2.1 = z₂.2.1 ∧
      |z₁.1 - z₂.1| ≤ 2 * C₁ * (X / L) ∧
      (∃ p₁ p₂ : ℕ, Work.BMF.IsPrimeIn P₁ (2 * P₁) p₁ ∧
        Work.BMF.IsPrimeIn P₁ (2 * P₁) p₂ ∧ p₁ ≠ p₂ ∧ ¬ p₁ ∣ z₁.2.1 ∧ ¬ p₂ ∣ z₂.2.1 ∧
        Work.BMF.EdgeGeom A.fam P₁ L ⟨e.x₁, e.x₂, p₁, p₂⟩ ∧
        Work.BMF.IntegralOn 1 (Work.BMF.dil (p₂ : ℝ) z₁.2.2.2.1 -
          Work.BMF.dil (p₁ : ℝ) z₂.2.2.2.1)) := by
    intro e he
    have heF : e ∈ A.edges :=
      (Finset.mem_filter.mp (show e ∈ A.edges.filter (fun e => ¬ badP e) from he)).1
    have hnb : ¬ badP e :=
      (Finset.mem_filter.mp (show e ∈ A.edges.filter (fun e => ¬ badP e) from he)).2
    obtain ⟨T, q₁, qf₁, γ₁, Ps₁, q₂, qf₂, γ₂, Ps₂, hg₁, hg₂, hint₀,
      ⟨z₁, hz₁F, hz₁q, hz₁mod, hz₁T⟩, ⟨z₂, hz₂F, hz₂q, hz₂mod, hz₂T⟩⟩ := h3 e heF
    have gz₁ : Work.BMF.GoodQuad A δ e.x₁ z₁.1 z₁.2.1 z₁.2.2.1 z₁.2.2.2.1 z₁.2.2.2.2 :=
      hgood e.x₁ z₁ hz₁F
    have gz₂ : Work.BMF.GoodQuad A δ e.x₂ z₂.1 z₂.2.1 z₂.2.2.1 z₂.2.2.2.1 z₂.2.2.2.2 :=
      hgood e.x₂ z₂ hz₂F
    have hint : Work.BMF.IntegralOn 1 (Work.BMF.dil (e.p₂ : ℝ) z₁.2.2.2.1 -
        Work.BMF.dil (e.p₁ : ℝ) z₂.2.2.2.1) := by
      obtain ⟨c₁, hc₁⟩ := dil_ModZConst_cp hz₁mod (e.p₂ : ℝ)
      obtain ⟨c₂, hc₂⟩ := dil_ModZConst_cp hz₂mod (e.p₁ : ℝ)
      have hconst : Work.BMF.IntegralOn 1
          (Polynomial.C (c₁:ℝ) - Polynomial.C (c₂:ℝ)) :=
        (Work.BMF.IntegralOn.const c₁).sub (Work.BMF.IntegralOn.const c₂)
      have heq : Work.BMF.dil (e.p₂ : ℝ) z₁.2.2.2.1 - Work.BMF.dil (e.p₁ : ℝ) z₂.2.2.2.1
          = (Work.BMF.dil (e.p₂ : ℝ) γ₁ - Work.BMF.dil (e.p₁ : ℝ) γ₂)
            + (Polynomial.C (c₁:ℝ) - Polynomial.C (c₂:ℝ)) := by
        rw [hc₁, hc₂]; ring
      rw [heq]
      exact hint₀.add hconst
    have hnb₁ : ∀ z ∈ F e.x₁, ¬ (e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1) :=
      fun z hz hc => hnb (Or.inl ⟨z, hz, hc⟩)
    have hnb₂ : ∀ z ∈ F e.x₂, ¬ (e.p₁ ∣ z.2.1 ∨ e.p₂ ∣ z.2.1) :=
      fun z hz hc => hnb (Or.inr ⟨z, hz, hc⟩)
    obtain ⟨hx₁fam, hx₂fam, _hne, hpne, hp₁in, hp₂in, _hgeo100⟩ := A.geom e heF
    have hqz : z₁.2.1 = z₂.2.1 :=
      Work.N8.goodQuad_q_eq A gz₁ gz₂ hp₁in.1 hp₂in.1 hint
        (fun hd => hnb₂ z₂ hz₂F (Or.inl hd))
        (fun hd => hnb₁ z₁ hz₁F (Or.inr hd))
    have hTclose : |z₁.1 - z₂.1| ≤ 2 * C₁ * (X / L) := by
      have h₁' : |z₁.1 - T| ≤ C₁ * (X / L) := hz₁T
      have h₂' : |z₂.1 - T| ≤ C₁ * (X / L) := hz₂T
      calc |z₁.1 - z₂.1| ≤ |z₁.1 - T| + |z₂.1 - T| := by
            have h := abs_sub_le z₁.1 T z₂.1
            rwa [abs_sub_comm T z₂.1] at h
        _ ≤ C₁ * (X/L) + C₁ * (X/L) := add_le_add h₁' h₂'
        _ = 2 * C₁ * (X/L) := by ring
    exact ⟨z₁, z₂, hz₁F, hz₂F, hqz, hTclose,
      e.p₁, e.p₂, hp₁in, hp₂in, hpne,
      (fun hd => hnb₁ z₁ hz₁F (Or.inl hd)),
      (fun hd => hnb₂ z₂ hz₂F (Or.inr hd)),
      A.geom e heF, hint⟩
  let fq : (e : Work.BMF.Edge) → e ∈ E' → ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ :=
    fun e he => Classical.choose (key e he)
  let gq : (e : Work.BMF.Edge) → e ∈ E' → ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ :=
    fun e he => Classical.choose (Classical.choose_spec (key e he))
  have hfg : ∀ (e : Work.BMF.Edge) (he : e ∈ E'),
      (fq e he) ∈ F e.x₁ ∧ (gq e he) ∈ F e.x₂ ∧ (fq e he).2.1 = (gq e he).2.1 ∧
      |(fq e he).1 - (gq e he).1| ≤ 2 * C₁ * (X / L) ∧
      (∃ p₁ p₂ : ℕ, Work.BMF.IsPrimeIn P₁ (2 * P₁) p₁ ∧
        Work.BMF.IsPrimeIn P₁ (2 * P₁) p₂ ∧ p₁ ≠ p₂ ∧ ¬ p₁ ∣ (fq e he).2.1 ∧
        ¬ p₂ ∣ (gq e he).2.1 ∧
        Work.BMF.EdgeGeom A.fam P₁ L ⟨e.x₁, e.x₂, p₁, p₂⟩ ∧
        Work.BMF.IntegralOn 1 (Work.BMF.dil (p₂ : ℝ) (fq e he).2.2.2.1 -
          Work.BMF.dil (p₁ : ℝ) (gq e he).2.2.2.1)) :=
    fun e he => Classical.choose_spec (Classical.choose_spec (key e he))
  let S : Finset ((ℝ × (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)) ×
                  (ℝ × (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ))) :=
    E'.attach.image (fun x => ((x.1.x₁, fq x.1 x.2), (x.1.x₂, gq x.1 x.2)))
  have hSdef : S = E'.attach.image (fun x => ((x.1.x₁, fq x.1 x.2), (x.1.x₂, gq x.1 x.2))) :=
    rfl
  refine ⟨S, ?_, ?_⟩
  · intro p hp
    rw [hSdef] at hp
    rw [Finset.mem_image] at hp
    obtain ⟨x, -, rfl⟩ := hp
    have hxE : x.1 ∈ A.edges :=
      (Finset.mem_filter.mp (show x.1 ∈ A.edges.filter (fun e => ¬ badP e) from x.2)).1
    obtain ⟨hx₁fam, hx₂fam, _, _, _, _, _⟩ := A.geom x.1 hxE
    obtain ⟨hfF, hgF, hqz, hT, hprimes⟩ := hfg x.1 x.2
    refine ⟨hx₁fam, hx₂fam, hfF, hgF, hqz, hT, ?_⟩
    obtain ⟨p₁, p₂, e1, e2, e3, e4, e5, e6, e7⟩ := hprimes
    exact ⟨p₁, p₂, e1, e2, e3, e4, e5, e6, e7⟩
  · have hinj : Set.InjOn (fun x : {e // e ∈ E'} =>
        ((x.1.x₁, fq x.1 x.2), (x.1.x₂, gq x.1 x.2))) ↑E'.attach := by
      intro x _ y _ hxy
      obtain ⟨a, ha⟩ := x
      obtain ⟨b, hb⟩ := y
      have haE : a ∈ A.edges :=
        (Finset.mem_filter.mp (show a ∈ A.edges.filter (fun e => ¬ badP e) from ha)).1
      have hbE : b ∈ A.edges :=
        (Finset.mem_filter.mp (show b ∈ A.edges.filter (fun e => ¬ badP e) from hb)).1
      have h1 : a.x₁ = b.x₁ := by
        have hh := congrArg (fun w => w.1.1) hxy
        simpa using hh
      have h2 : a.x₂ = b.x₂ := by
        have hh := congrArg (fun w => w.2.1) hxy
        simpa using hh
      obtain ⟨hp1, hp2⟩ := huniq a haE b hbE h1 h2
      refine Subtype.ext ?_
      cases a with
      | mk a₁ a₂ a₃ a₄ =>
      cases b with
      | mk b₁ b₂ b₃ b₄ =>
      rw [Work.BMF.Edge.mk.injEq]
      exact ⟨h1, h2, hp1, hp2⟩
    have hcard : S.card = E'.card := by
      have hcc := Finset.card_image_of_injOn hinj
      rw [hSdef, hcc, Finset.card_attach]
    have hEdges : c * Work.BMF.pi0 P₁ ^ 2 * (X / L) ≤ (A.edges.card : ℝ) := A.edges_card
    have hsplit : ((A.edges.filter badP).card : ℝ) + (E'.card : ℝ) = (A.edges.card : ℝ) := by
      have hcf := Finset.card_filter_add_card_filter_not (s := A.edges) (p := badP)
      rw [← hE'def] at hcf
      exact_mod_cast hcf
    have hXLnn : 0 ≤ X / L := div_nonneg (le_of_lt hX) (by linarith)
    rw [hcard]
    have hPnn : 0 ≤ c * (X / L) * Work.BMF.pi0 P₁ ^ 2 :=
      mul_nonneg (mul_nonneg (le_of_lt hc) hXLnn) (sq_nonneg _)
    have h1 : c / 4 * (X / L) * Work.BMF.pi0 P₁ ^ 2
        ≤ c * Work.BMF.pi0 P₁ ^ 2 * (X / L) / 2 := by
      rw [show c / 4 * (X / L) * Work.BMF.pi0 P₁ ^ 2
            = c * (X / L) * Work.BMF.pi0 P₁ ^ 2 / 4 by ring,
          show c * Work.BMF.pi0 P₁ ^ 2 * (X / L) / 2
            = c * (X / L) * Work.BMF.pi0 P₁ ^ 2 / 2 by ring]
      linarith
    have h2 : c * Work.BMF.pi0 P₁ ^ 2 * (X / L) / 2 ≤ (A.edges.card : ℝ) / 2 := by
      linarith
    have h3 : (A.edges.card : ℝ) / 2 ≤ (E'.card : ℝ) := by linarith
    linarith

end Work.N8
