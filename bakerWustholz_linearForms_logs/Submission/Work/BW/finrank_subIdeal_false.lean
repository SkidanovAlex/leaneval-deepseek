import Mathlib
import Submission.Work.BW.finrank_subIdeal_false_defs
import Submission.Work.BW.char_linearIndependent
import Submission.Work.BW.eval_mono_eq_of_rowLat
import Submission.Work.BW.xmono_linearIndependent
import Submission.Work.BW.xmono_span

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

noncomputable section

/-! ### General linear-algebra assembly -/

/-- If a finite family `x` of vectors of `V` is linearly independent modulo `I'` (`hind`) and its
image spans `V ⧸ I'` (`hspan`), then `V ⧸ I'` has dimension `Fintype.card ι`. -/
theorem finrank_quot_eq_card_of {V : Type*} [AddCommGroup V] [Module ℂ V]
    (I' : Submodule ℂ V) {ι : Type*} [Fintype ι] (x : ι → V)
    (hind : ∀ g : ι → ℂ, (∑ i, g i • x i) ∈ I' → ∀ i, g i = 0)
    (hspan : ⊤ ≤ Submodule.span ℂ
      (Set.range (fun i => (Submodule.mkQ I') (x i)))) :
    Module.finrank ℂ (V ⧸ I') = Fintype.card ι := by
  have hi : LinearIndependent ℂ (fun i => (Submodule.mkQ I') (x i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : (Submodule.mkQ I') (∑ i, g i • x i)
        = ∑ i, g i • (Submodule.mkQ I') (x i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
    have hker : (Submodule.mkQ I') (∑ i, g i • x i) = 0 := by rw [hsum, hg]
    have hg' : (∑ i, g i • x i) ∈ I' := by
      rw [← Submodule.ker_mkQ I']
      exact LinearMap.mem_ker.mpr hker
    exact hind g hg'
  exact Module.finrank_eq_card_basis (Module.Basis.mk hi hspan)

/-- The Hilbert function of the coordinate ring of the closure of `G' = {0} × ker 𝒵` in multidegree `d`: the graded piece `(R/I)_d` has dimension exactly `#(classes of the box ∏ᵢ[0,d_{i+1}] mod 𝒵)`.

Here `I = subIdeal N ρ false M` is the multihomogeneous vanishing ideal of `G' = {0} × ker 𝒵` (`𝒵` = row lattice of `M`, `PrimSys M`), and the graded piece is `homPiece N d ⧸ (I ⊓ homPiece N d)`, i.e. `Submodule.comap (homPiece N d).subtype (I.restrictScalars ℂ)`.

Route (hints, all ingredients available elsewhere in the workspace): membership of a multihomogeneous `F` in `subIdeal` is exactly vanishing at the cone points of `InSub`; the monomials `mono N d b`, `bᵢ ≤ dᵢ`, span `homPiece N d` (`Submission.Work.BW.span_mono`); `X_{0,1} ∈ I` when `ε = false`, so every `mono N d b` with `b 0 ≥ 1` lies in `I`; monomials with equal `b 0` and torus parts congruent mod `rowLat` agree on `ker 𝒵` (`Submission.Work.BW.eval_mono_eq_of_rowLat`); distinct classes give linearly independent characters (`Submission.Work.BW.char_linearIndependent`). The class of a point `(bᵢ)_{i≥1}` is `clsOf N ρ M (torPart b)`, and the number of classes realized is `boxClassCount N ρ M (fun i => d i.succ)` (`Submission.Work.BW.card_fib_false`).

Concretely: choose one representative exponent vector `rep c ∈ {b ∈ degBox N d | b 0 = 0}` for each realized class `c`; these span `homPiece N d` modulo `I ⊓ homPiece N d` and are linearly independent there, so the dimension equals the number of realized classes. -/
theorem finrank_subIdeal_false {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (hM : PrimSys M) :
    Module.finrank ℂ (homPiece N d ⧸ Submodule.comap (homPiece N d).subtype
        ((subIdeal N ρ false M).restrictScalars ℂ))
      = boxClassCount N ρ M (fun i => d i.succ) := by
  have hmain : Module.finrank ℂ (homPiece N d ⧸ Submodule.comap (homPiece N d).subtype
        ((subIdeal N ρ false M).restrictScalars ℂ)) = Fintype.card (clsSet d M) :=
    finrank_quot_eq_card_of (subPiece N ρ d M) (xmono d M)
      (xmono_linearIndependent d M hM) (xmono_span d M)
  rw [hmain, Fintype.card_coe]
  rfl

end

end Work.BW
