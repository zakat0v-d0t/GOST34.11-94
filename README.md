# cryptolib

Модуль на C для Python, реализующий алгоритмы хэширования:
- ГОСТ Р 34.11-94 (256 бит, S-box D-A / CryptoPro, совместим с Bouncy Castle)
- RIPEMD-128
- RIPEMD-256
- RIPEMD-320

Реализован на C через CPython C-API для быстрого расчета на больших объемах данных (освобождает GIL, передает буферы без копирования памяти). Интерфейс сделан аналогично стандартному `hashlib`.

## Сборка

Для сборки нужен `gcc` и заголовочные файлы Python (`python3-dev`):

```bash
gcc -O3 -shared -fPIC $(python3-config --includes) cryptolib.c -o cryptolib.so
```

После компиляции рядом появится файл `cryptolib.so`, который можно сразу импортировать в Python.

## Использование

```python
import cryptolib

# Хэширование строки в одну строчку
h = cryptolib.gost3411(b"Hello world")
print(h.hexdigest())

# Потоковое хэширование (частями)
hasher = cryptolib.ripemd320()
hasher.update(b"часть 1")
hasher.update(b"часть 2")

print(hasher.digest())     # байты
print(hasher.hexdigest())  # hex-строка
```

Все объекты поддерживают методы:
- `update(data)` — добавить данные (bytes / bytearray).
- `digest()` — получить хэш в виде байтов.
- `hexdigest()` — получить хэш в виде шестнадцатеричной строки.
- `copy()` — создать копию текущего состояния хэшера.

А также атрибуты `digest_size`, `block_size` и `name`.
