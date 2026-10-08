import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.Fitting.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical

namespace Work.GlaubermanZJ

open Work.Fitting

/-- `O_π(G/K) = 1` for a normal subgroup `K` of `G` that is a `π`-group and contains every
normal `π`-subgroup of `G`.

This is the general form of `Work.Fitting.piCore_quotient_eq_bot` (the case `K = O_π(G)`):
if `M` is a normal `π`-subgroup of `G/K`, its preimage `M.comap (mk' K)` is a normal subgroup
of `G` of order `|K| · |M|`, hence a `π`-number, so by maximality it lies in `K`; applying
`mk' K` gives `M = 1`.  The proof is that of `Work.Fitting.piCore_quotient_eq_bot`, with the
two facts about `O_π(G)` (that it is a `π`-group, and that it contains every normal
`π`-subgroup) abstracted into the hypotheses `hKpi` and `hKmax`. -/
theorem piCore_quotient_eq_bot_of {G : Type*} [Group G] [Finite G] (π : ℕ → Prop)
    (K : Subgroup G) [K.Normal]
    (hKpi : IsPiNat π (Nat.card ↥K))
    (hKmax : ∀ N : Subgroup G, N.Normal → IsPiNat π (Nat.card ↥N) → N ≤ K) :
    piCore π (G ⧸ K) = ⊥ := by
  set f : G →* G ⧸ K := QuotientGroup.mk' K with hfdef
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective K
  have hker : f.ker = K := QuotientGroup.ker_mk' K
  refine le_antisymm ?_ bot_le
  rw [piCore]
  refine sSup_le fun M hM => ?_
  rw [mem_piCoreSet] at hM
  obtain ⟨hMnormal, hMpi⟩ := hM
  haveI : M.Normal := hMnormal
  have hrange : M ≤ f.range := by
    rw [MonoidHom.range_eq_top.mpr hsurj]; exact le_top
  have hcomap_norm : (M.comap f).Normal := Subgroup.normal_comap f
  have hcard : Nat.card ↥(M.comap f) = Nat.card ↥K * Nat.card ↥M := by
    have h := card_comap_eq_card_ker_mul f hsurj M
    rw [hker] at h
    exact h
  have hcomapπ : IsPiNat π (Nat.card ↥(M.comap f)) := by
    rw [hcard]; exact IsPiNat.mul hKpi hMpi
  have hle : M.comap f ≤ K := hKmax _ hcomap_norm hcomapπ
  have hmap : Subgroup.map f (M.comap f) = M := Subgroup.map_comap_eq_self hrange
  have hmapK : Subgroup.map f K = ⊥ := (Subgroup.map_eq_bot_iff K).mpr (le_of_eq hker.symm)
  calc M = Subgroup.map f (M.comap f) := hmap.symm
    _ ≤ Subgroup.map f K := Subgroup.map_mono hle
    _ = ⊥ := hmapK

-- `O_{p'}(G ⧸ O_{p'}(G)) = 1`.  (Wrapper around `Work.Fitting.piCore_quotient_eq_bot`.)
theorem pPrimeCore_quotient_eq_bot {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    [(Submission.Blueprint.pPrimeCore p G).Normal] :
    Work.Fitting.pPrimeCore p (G ⧸ Submission.Blueprint.pPrimeCore p G) = ⊥ := by
  have hK : Submission.Blueprint.pPrimeCore p G = Work.Fitting.piCore (fun q => q ≠ p) G :=
    pPrimeCore_eq_fitting p hp
  have hKpi : IsPiNat (fun q => q ≠ p)
      (Nat.card ↥(Submission.Blueprint.pPrimeCore p G)) := by
    rw [hK]; exact piCore_isPiNat G (fun q => q ≠ p)
  have hKmax : ∀ N : Subgroup G, N.Normal → IsPiNat (fun q => q ≠ p) (Nat.card ↥N) →
      N ≤ Submission.Blueprint.pPrimeCore p G := by
    intro N hN hNpi
    rw [hK]
    exact le_piCore hN hNpi
  exact piCore_quotient_eq_bot_of (fun q => q ≠ p)
    (Submission.Blueprint.pPrimeCore p G) hKpi hKmax

end Work.GlaubermanZJ
