import Mathlib

namespace Work.WilC5

theorem existsUnique_realize_of_defines {L : FirstOrder.Language} {M N : Type} [L.Structure M]
    [L.Structure N] {γ : Type} (ii : γ → M) (jj : γ → N)
    (H : ∀ φ : L.Formula γ, φ.Realize ii ↔ φ.Realize jj)
    (φ : L.Formula (γ ⊕ Fin 1)) (s : M)
    (hφ : ∀ v : Fin 1 → M, v 0 = s ↔ φ.Realize (Sum.elim ii v)) :
    ∃! n : N, φ.Realize (Sum.elim jj (fun _ => n)) := by
  -- The γ-formula `iExsUnique` expresses "there is a unique assignment to the extra
  -- variable satisfying φ".
  -- On the M side this holds by `hφ`, since the only assignment making φ true is the
  -- constant one with value `s`.
  have hM : (φ.iExsUnique (Fin 1)).Realize ii := by
    rw [FirstOrder.Language.Formula.realize_iExsUnique]
    refine ⟨fun _ => s, (hφ _).mp rfl, ?_⟩
    intro i hi
    funext x
    have h0 : i 0 = s := (hφ i).mpr hi
    rw [show x = 0 from Subsingleton.elim x 0]
    exact h0
  -- Transfer to N using the hypothesis `H`.
  have hN : (φ.iExsUnique (Fin 1)).Realize jj := (H (φ.iExsUnique (Fin 1))).mp hM
  rw [FirstOrder.Language.Formula.realize_iExsUnique] at hN
  obtain ⟨i₀, hi₀, huniq⟩ := hN
  -- An assignment `Fin 1 → N` is determined by its value at `0`, giving the `∃!` over `N`.
  refine ⟨i₀ 0, ?_, ?_⟩
  · change φ.Realize (Sum.elim jj (fun _ : Fin 1 => i₀ 0))
    have hfun : (fun _ : Fin 1 => i₀ 0) = i₀ := by
      funext x; rw [show x = 0 from Subsingleton.elim x 0]
    rw [hfun]; exact hi₀
  · intro n hn
    have hfun : (fun _ : Fin 1 => n) = i₀ := huniq _ hn
    simpa using congrFun hfun 0

end Work.WilC5
