import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.CyclicNotDvd
import Submission.Work.CORE4.PGroupActionCentralizer

set_option linter.style.haveILetI false

namespace Work.CORE4

/-!
# `Work.CORE4.CopyLocalPPart`

`p² ∤ |D|` in the "copy" configuration `W = P × E` of Bender (1981) §4, p. 227: `P` has order
the prime `p` and commutes elementwise with `E`, `P ⊓ E = ⊥`, `D ≤ P ⊔ E` meets `P` trivially,
`X ≤ D` has order `p` and meets `E` trivially, and `N_D(X)` is cyclic.

Math.  `P ⊔ E = P · E` is an internal direct product, and `E` is normal in it, so `D ≤ N_G(E)`
and `X ≤ N_G(E)`.  The cardinality form of the second isomorphism theorem
(`card_sup_mul_card_inf_of_le_normalizer`) gives `|E ⊔ P| = p·|E|` and `|E ⊔ X| = |X|·|E| = p·|E|`;
since `X ⊔ E ≤ P ⊔ E`, this forces `X ⊔ E = P ⊔ E`, whence `D ⊔ E = P ⊔ E`.  Applying the same
formula to `(E, D)` yields `|D|·|E| = |P ⊔ E|·|D ⊓ E| = p·|E|·|D ⊓ E|`, i.e.
`|D| = p·|D ⊓ E|`.

It remains to see `p ∤ |D ⊓ E|`.  Put `K := D ⊓ E`.  Since `D ≤ N_G(E)` we have `K ⊴ D` (and
`X ≤ N_G(K)`), so `X` acts on `K` by conjugation.  Orbit counting for the action of the
`p`-group `X` gives `|K| ≡ |C_K(X)| (mod p)`, so `p ∣ |K|` would force `p ∣ |C_K(X)|`.  But
`C_K(X) ≤ D ⊓ N_G(X)`, which is cyclic, and `C_K(X) ⊓ X ≤ E ⊓ X = ⊥`; in a cyclic group the
subgroup of order `p` is unique, so `p ∤ |C_K(X)|` — a contradiction.  Hence `p ∤ |D ⊓ E|` and
`|D| = p·|D ⊓ E|` is divisible by `p` but not by `p²`.
-/

/-- `|A ⊔ B| · |A ⊓ B| = |A| · |B|` when `B ≤ N_G(A)`: the cardinality shadow of the second
isomorphism theorem.  (Self-contained copy, so that this module only depends on Mathlib.) -/
private theorem card_sup_mul_card_inf_of_le_normalizer' {G : Type*} [Group G] [Finite G]
    {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hAB : (A ⊓ B).subgroupOf B = A.subgroupOf B := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have h1 : (A.subgroupOf B).index * Nat.card ↥(A ⊓ B) = Nat.card ↥B := by
    have hc : Nat.card ↥(A.subgroupOf B) = Nat.card ↥(A ⊓ B) := by
      rw [← hAB]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ B ≤ B)).toEquiv
    rw [← hc]
    exact Subgroup.index_mul_card (A.subgroupOf B)
  have h2 : (A.subgroupOf (A ⊔ B)).index * Nat.card ↥A = Nat.card ↥(A ⊔ B) := by
    have hc : Nat.card ↥(A.subgroupOf (A ⊔ B)) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B)).toEquiv
    rw [← hc]
    exact Subgroup.index_mul_card (A.subgroupOf (A ⊔ B))
  have hidx : (A.subgroupOf B).index = (A.subgroupOf (A ⊔ B)).index := by
    haveI := Subgroup.normal_subgroupOf_of_le_normalizer h
    haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
    have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B A h
    rw [Subgroup.index_eq_card (A.subgroupOf B),
      Subgroup.index_eq_card (A.subgroupOf (A ⊔ B)), sup_comm]
    exact Nat.card_congr e.toEquiv
  calc Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)
      = ((A.subgroupOf (A ⊔ B)).index * Nat.card ↥A) * Nat.card ↥(A ⊓ B) := by rw [h2]
    _ = ((A.subgroupOf B).index * Nat.card ↥A) * Nat.card ↥(A ⊓ B) := by rw [hidx]
    _ = Nat.card ↥A * ((A.subgroupOf B).index * Nat.card ↥(A ⊓ B)) := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [h1]

/-- `p² ∤ |D|` in the copy configuration `D ≤ P ⊔ E` with `|P| = p`, `D ⊓ P = ⊥`, and an
order-`p` subgroup `X ≤ D` with `X ⊓ E = ⊥` and cyclic `N_D(X)`. -/
theorem CopyLocalPPart {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P E D X : Subgroup G}
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) (hinf : P ⊓ E = ⊥)
    (hDP : D ≤ P ⊔ E) (hbot : D ⊓ P = ⊥) (hPcard : Nat.card P = p)
    (hXcard : Nat.card X = p) (hXD : X ≤ D) (hXE : X ⊓ E = ⊥)
    (hcyc : IsCyclic ↥(D ⊓ Subgroup.normalizer (X : Set G))) :
    ¬ p ^ 2 ∣ Nat.card ↥D := by
  classical
  -- ## The normalizer facts: `P`, `E` commute, so `E ⊴ P ⊔ E`, hence `D ≤ N_G(E)`, `X ≤ N_G(E)`.
  have hPnorm : P ≤ Subgroup.normalizer (E : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer (E : Set G)
      (Subgroup.mem_centralizer_iff.mpr (fun y hy => (hcomm x hx y hy).symm))
  have hPEnorm : (P ⊔ E : Subgroup G) ≤ Subgroup.normalizer (E : Set G) :=
    sup_le hPnorm Subgroup.le_normalizer
  have hDnorm : D ≤ Subgroup.normalizer (E : Set G) := hDP.trans hPEnorm
  have hXnorm : X ≤ Subgroup.normalizer (E : Set G) := hXD.trans hDnorm
  -- ## `|P ⊔ E| = p·|E|` and `|X ⊔ E| = p·|E|`.
  have hPEcard : Nat.card ↥(P ⊔ E) = Nat.card ↥E * p := by
    have h := card_sup_mul_card_inf_of_le_normalizer' (A := E) (B := P) hPnorm
    rw [sup_comm E P, inf_comm E P, hinf, Subgroup.card_bot, mul_one, hPcard] at h
    exact h
  have hXEcard : Nat.card ↥(X ⊔ E) = Nat.card ↥E * p := by
    have h := card_sup_mul_card_inf_of_le_normalizer' (A := E) (B := X) hXnorm
    rw [sup_comm E X, inf_comm E X, hXE, Subgroup.card_bot, mul_one, hXcard] at h
    exact h
  -- ## `X ⊔ E = P ⊔ E` and hence `D ⊔ E = P ⊔ E`.
  have hsupXE : X ⊔ E = P ⊔ E := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le (hXD.trans hDP) le_sup_right) ?_
    rw [hPEcard, hXEcard]
  have hsupDE : D ⊔ E = P ⊔ E := by
    refine le_antisymm (sup_le hDP le_sup_right) ?_
    rw [← hsupXE]
    exact sup_le (le_trans hXD le_sup_left) le_sup_right
  -- ## `|D| · |E| = |P ⊔ E| · |D ⊓ E|`.
  have hmul : Nat.card ↥D * Nat.card ↥E = Nat.card ↥(P ⊔ E) * Nat.card ↥(D ⊓ E) := by
    have h := card_sup_mul_card_inf_of_le_normalizer' (A := E) (B := D) hDnorm
    rw [sup_comm E D, hsupDE, inf_comm E D] at h
    rw [mul_comm (Nat.card ↥D) (Nat.card ↥E)]
    exact h.symm
  -- ## `|D| = p · |D ⊓ E|`.
  have hDcard : Nat.card ↥D = p * Nat.card ↥(D ⊓ E) := by
    have hEpos : 0 < Nat.card ↥E := Nat.card_pos
    have hmain : Nat.card ↥E * Nat.card ↥D = Nat.card ↥E * (p * Nat.card ↥(D ⊓ E)) := by
      calc Nat.card ↥E * Nat.card ↥D
          = Nat.card ↥D * Nat.card ↥E := by ring
        _ = Nat.card ↥(P ⊔ E) * Nat.card ↥(D ⊓ E) := hmul
        _ = (Nat.card ↥E * p) * Nat.card ↥(D ⊓ E) := by rw [hPEcard]
        _ = Nat.card ↥E * (p * Nat.card ↥(D ⊓ E)) := by ring
    exact Nat.mul_left_cancel hEpos hmain
  -- ## `p ∤ |D ⊓ E|`.
  have hKndvd : ¬ p ∣ Nat.card ↥(D ⊓ E) := by
    intro hdvd
    -- `X` normalizes `K := D ⊓ E`
    have hXK : X ≤ Subgroup.normalizer ((D ⊓ E : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro k
      have hxD : x ∈ D := hXD hx
      have hxN : x ∈ Subgroup.normalizer (E : Set G) := hXnorm hx
      constructor
      · intro hk
        exact ⟨D.mul_mem (D.mul_mem hxD hk.1) (D.inv_mem hxD),
          (Subgroup.mem_normalizer_iff.mp hxN k).mp hk.2⟩
      · intro hk
        obtain ⟨hd, he⟩ := hk
        refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hxN k).mpr he⟩
        have hmem : x⁻¹ * (x * k * x⁻¹) * x ∈ D :=
          D.mul_mem (D.mul_mem (D.inv_mem hxD) hd) hxD
        have heq : x⁻¹ * (x * k * x⁻¹) * x = k := by group
        rwa [heq] at hmem
    have hcentral : p ∣ Nat.card ↥((D ⊓ E) ⊓ Subgroup.centralizer (X : Set G)) :=
      PGroupActionCentralizer (K := D ⊓ E) hp hXK hXcard hdvd
    -- the three side conditions for the cyclic lemma
    have hXN : X ≤ D ⊓ Subgroup.normalizer (X : Set G) :=
      fun x hx => ⟨hXD hx, Subgroup.le_normalizer hx⟩
    have hCN : (D ⊓ E) ⊓ Subgroup.centralizer (X : Set G) ≤
        D ⊓ Subgroup.normalizer (X : Set G) :=
      fun c hc => ⟨hc.1.1, Subgroup.centralizer_le_normalizer (X : Set G) hc.2⟩
    have hCX : ((D ⊓ E) ⊓ Subgroup.centralizer (X : Set G)) ⊓ X = ⊥ := by
      refine eq_bot_iff.mpr ?_
      have hle : ((D ⊓ E) ⊓ Subgroup.centralizer (X : Set G)) ⊓ X ≤ (E ⊓ X : Subgroup G) :=
        le_trans (inf_le_inf_right X inf_le_left) (inf_le_inf_right X inf_le_right)
      rw [inf_comm E X, hXE] at hle
      exact hle
    exact CyclicNotDvd (N := D ⊓ Subgroup.normalizer (X : Set G))
      (C := (D ⊓ E) ⊓ Subgroup.centralizer (X : Set G)) hp hcyc hXcard hXN hCN hCX hcentral
  -- ## Conclusion.
  intro hdiv
  rw [hDcard, pow_two] at hdiv
  exact hKndvd ((Nat.mul_dvd_mul_iff_left hp.pos).mp hdiv)

end Work.CORE4
