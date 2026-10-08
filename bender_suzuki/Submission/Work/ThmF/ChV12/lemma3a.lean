import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.Bender.Basic
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.DTransitiveInv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- Elementwise form of the conjugation computation used in `lemma3a`: if `d u d⁻¹ = s` and
`w` commutes with `s`, then `d⁻¹ w d` commutes with `u`. -/
private lemma conj_image_key {G : Type} [Group G] (d u s w : G) (hdu : d * u * d⁻¹ = s)
    (hws : w * s = s * w) :
    (d⁻¹ * w * d) * u * (d⁻¹ * w * d)⁻¹ = u := by
  have h1 : (d⁻¹ * w * d) * u * (d⁻¹ * w * d)⁻¹
      = d⁻¹ * (w * (d * u * d⁻¹) * w⁻¹) * d := by group
  rw [h1, hdu, show w * s * w⁻¹ = s by rw [hws]; group]
  rw [← hdu]
  group

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem lemma3a {G : Type} [Group G] [Finite G] (hS : Situation G) (hC4 : ChIIFourProp) (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t) (s : G) (hs : s ∈ Q) (hs2 : orderOf s = 2) (hD : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G), ∃ d ∈ twoPoint H t, d * a * d⁻¹ = b) (hsv : ∀ v ∈ centD H t, v * s = s * v) : centD H t = twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) := by
  -- Ch. II §4 Prop. 2 (a): `V = C_D(u)` for an involution `u ∈ H`.
  obtain ⟨u, hu, hVu⟩ := (hC4 G hS H h.stronglyEmbedded t h.invol h.not_mem).2.1
  have hsH : s ∈ H := h.le hs
  have hsinv : s ∈ involutions (H : Set G) := ⟨hsH, hs2⟩
  -- `D` is transitive on `Inv(H)`, so `s = d u d⁻¹` for some `d ∈ D`.
  obtain ⟨d, hd, hdu⟩ := hD u hu s hsinv
  -- The hypothesis `hsv` gives `V ≤ C_D(s)`.
  have hVCs : centD H t ≤ twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) := by
    intro v hv
    refine ⟨(Subgroup.mem_inf.mp hv).1, ?_⟩
    change v ∈ Subgroup.centralizer ({s} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hsv v hv
  -- Conjugation by `d` embeds `C_D(s)` into `C_D(u) = V`.
  have hmem : ∀ w : ↥(twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G)),
      d⁻¹ * (w : G) * d ∈ twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) := by
    intro w
    rcases Subgroup.mem_inf.mp w.2 with ⟨hwD, hwC⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (twoPoint H t).mul_mem ((twoPoint H t).mul_mem ((twoPoint H t).inv_mem hd) hwD) hd
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hws : (w : G) * s = s * (w : G) := Subgroup.mem_centralizer_singleton_iff.mp hwC
      have key := conj_image_key d u s (w : G) hdu hws
      calc (d⁻¹ * (w : G) * d) * u
          = ((d⁻¹ * (w : G) * d) * u * (d⁻¹ * (w : G) * d)⁻¹) * (d⁻¹ * (w : G) * d) := by
            group
        _ = u * (d⁻¹ * (w : G) * d) := by rw [key]
  have hinj : Function.Injective
      (fun w : ↥(twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G)) =>
        (⟨d⁻¹ * (w : G) * d, hmem w⟩ :
          ↥(twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)))) := by
    intro a b hab
    apply Subtype.ext
    have hab' : d⁻¹ * (a : G) * d = d⁻¹ * (b : G) * d := by
      have := congrArg
        (fun z : ↥(twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)) => (z : G)) hab
      simpa using this
    calc (a : G) = d * (d⁻¹ * (a : G) * d) * d⁻¹ := by group
      _ = d * (d⁻¹ * (b : G) * d) * d⁻¹ := by rw [hab']
      _ = (b : G) := by group
  have hcard : Nat.card ↥(twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G)) ≤
      Nat.card ↥(centD H t) := by
    rw [hVu]
    exact Nat.card_le_card_of_injective _ hinj
  -- `V ≤ C_D(s)` and `|V| = |C_D(s)|` force equality.
  exact Subgroup.eq_of_le_of_card_ge hVCs hcard

end Work.ThmF.ChV12
